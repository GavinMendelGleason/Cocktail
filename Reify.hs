module Reify where 

import Lang
import Derivation
import Eval 
import Exceptions
import Data.List
import Control.Monad
import Data.Maybe
import Generalise
import Soundness
import Debug.Trace
import Utils
import Control.Monad.Error
import Data.Foldable (foldrM)
import Normalise 

recurrenceSequents d = let h@(Holds fctx _ _ _ _) = proofSequent d
                           ps = paths d
                       in map (listToMaybe . reverse) ps


type Index = Int
type Funs = [(Index,String,Holds,[Var],[TVar])]

funName (i,f,h,xs,txs) = f
fraise fs = map (\ (i,f,h,xs,txs) -> (i+1,f,h,xs,txs)) fs

reify :: MonadError String m => PreProof -> Funs -> m (Term,FunCtx)
reify d fs = let h@(Holds fctx vctx tctx t ty) = proofSequent d
                 hs = recurrenceSequents d
             in if not (null hs)
                then do 
                  let (ftvs,fvs) = freevars vctx t
                  let f = freshen "f" $ map funName fs
                  (tnew,fctx) <- reify' d ((0,f,h,fvs,ftvs):fs) 
                  let fapp = foldl (\ f i -> App f (V i)) (F f) (reverse fvs)
                  let fapp' = foldl (\ f i  -> TApp f (TV i)) fapp (reverse ftvs)
                  let strongt = strengthenTerm fvs ftvs tnew
                  vs <- maybeToError (foldrM (\ i r -> do 
                                                (v,ty) <- ith i vctx
                                                let ty' = strengthenType ftvs ty           
                                                return ((v,ty'):r)) [] fvs) $ "Corrupted context:"++show h
                  tvs <- maybeToError (foldrM (\ i r -> do 
                                                 tyn <- ith i tctx
                                                 return (tyn:r)) [] ftvs) $ "Corrupted context:"++show h
                  let ty1 = foldr (\ (v,ty) r -> Imp ty r) ty (reverse vs)
                  let ft = foldr (\ (v,ty) t -> Lambda v ty t) strongt (reverse vs)
                  let ty2 = foldr (\ v r -> All v r) ty1 (reverse tvs)
                  let fabs = foldr (\ v t -> TLambda v t) ft (reverse tvs)
                  return (fapp',(f,fabs,ty2):fctx)
                else reify' d fs

reify' :: MonadError String m => PreProof -> Funs -> m (Term,FunCtx)
reify' (VarIntro (Holds _ _ _ v _)) fs = do 
  return (v,[])
reify' (Pointer h n l) fs =
  maybeToError (do 
                 (i,f,h',l,tl) <- find (\ (j,_,_,_,_) -> j==n) fs
                 sub <- (h' >- h)
                 tsub <- (h' >*- h)
                 args <- mapM (\ i -> fmap snd (find (\ (j,_) -> (j==i)) sub)) l
                 targs <- mapM (\ i -> fmap snd (find (\ (j,_) -> (j==i)) tsub)) tl
                 let fapp = foldl (\ f t -> App f t) (F f) (reverse args)
                 let fapp' = foldl (\ f t -> TApp f t) fapp (reverse targs)
                 return (fapp',[])) $ "Corrupted Recurrance: "++ show (Pointer h n l) 
reify' (FunIntro (Holds _ _ _ f _)) fs = do 
  return (f,[])
reify' (UnitIntro h) fs = do
  return (Unit,[])
reify' (ImpElim h d e) fs = do 
  (t1,fctx1) <- reify d (fraise fs)
  (t2,fctx2) <- reify e (fraise fs)
  return (App t1 t2,fctx1++fctx2)
reify' (ImpIntro (Holds _ _ _ (Lambda x ty _) _) d) fs = do 
  (t1,fctx) <- reify d (fraise fs)
  return (Lambda x ty t1, fctx) 
reify' (AllIntro (Holds _ _ _ (TLambda x _) _) d) fs = do 
  (t1,fctx) <- reify d (fraise fs)
  return (TLambda x t1,fctx) 
reify' (AllElim (Holds _ _ _ (TApp _ ty) _) d) fs = do 
  (t1,fctx) <- reify d (fraise fs)
  return (TApp t1 ty,fctx) 
reify' (AndIntro h d e) fs = do 
  (t1,fctx1) <- reify d (fraise fs) 
  (t2,fctx2) <- reify e (fraise fs) 
  return (Pair t1 t2,fctx1++fctx2)
reify' (AndElim (Holds _ _ _ (Split _ x y _) _) d e) fs = do 
  (t1,fctx1) <- reify d (fraise fs) 
  (t2,fctx2) <- reify e (fraise fs) 
  return (Split t1 x y t2,fctx1++fctx2) 
reify' (AlphaIntro (Holds _ _ _ (Fold _ ty) _) d) fs = do 
  (t1,fctx) <- reify d (fraise fs) 
  return (Fold t1 ty,fctx) 
reify' (AlphaElim (Holds _ _ _ (Unfold _ ty) _)  d) fs = do 
  (t1,fctx) <- reify d (fraise fs) 
  return (Unfold t1 ty,fctx) 
reify' (OrIntroL (Holds _ _ _ (Inl _ ty) _) d) fs = do 
  (t1,fctx) <- reify d (fraise fs)
  return (Inl t1 ty,fctx)
reify' (OrIntroR (Holds _ _ _ (Inr _ ty) _) d) fs = do 
  (t1,fctx) <- reify d (fraise fs)
  return (Inr t1 ty,fctx)
reify' (OrElim (Holds _ _ _ (Case _ x _ y _) _) d e f) fs = do
  (t1,fctx1) <- reify d (fraise fs) 
  (t2,fctx2) <- reify e (fraise fs) 
  (t3,fctx3) <- reify f (fraise fs)
  return (Case t1 x t2 y t3,fctx1++fctx2++fctx3)
reify' (DeltaRule _ d) fs = reify d (fraise fs)
