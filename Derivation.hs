module Derivation where 

import Lang 
import Eval
import Exceptions
import Data.Maybe 
import Pretty 
import Data.List
import Utils 
import Choice 
import Control.Monad
import Control.Monad.Error
import Data.Foldable (foldrM) 
import Debug.Trace

data PreProof = Pointer Holds Int [PreProof] 
              | DeltaRule Holds PreProof
              | VarIntro Holds
              | FunIntro Holds 
              | UnitIntro Holds 
              --  | Incomplete Holds -- for incompletely developed proofs
              | ImpElim Holds PreProof PreProof
              | ImpIntro Holds PreProof
              | AllIntro Holds PreProof
              | AllElim Holds  PreProof
              | AndIntro Holds PreProof PreProof
              | AndElim Holds PreProof PreProof 
              | AlphaIntro Holds PreProof
              | AlphaElim Holds PreProof 
              | OrIntroL Holds PreProof
              | OrIntroR Holds PreProof
              | OrElim Holds PreProof PreProof PreProof deriving Show
                
proofSequent :: PreProof -> Holds
proofSequent (Pointer h n l) = h
proofSequent (VarIntro h) = h
proofSequent (FunIntro h) = h
proofSequent (UnitIntro h) = h
proofSequent (OrIntroL h a) = h
proofSequent (OrIntroR h a) = h
proofSequent (OrElim h a b c) = h
proofSequent (AlphaElim h a) = h 
proofSequent (AlphaIntro h a) = h
proofSequent (ImpIntro h a) = h
proofSequent (ImpElim h a b) = h
proofSequent (AndIntro h a b) = h
proofSequent (AndElim h a b) = h
proofSequent (AllElim h a) = h
proofSequent (AllIntro h a) = h
proofSequent (DeltaRule h a) = h

sequentType (Holds fctx ctx tctx t ty) = ty

sequentTerm (Holds fctx ctx tctx t ty) = t

{-
positive' :: Type -> Int -> (Bool,[Int],[Int])
positive' One = (True,[],[])
positive' (TV i) d = if i == d then (True,[i],[]) else (True,[],[i])
positive' (And r s) d = 
    let (rb,rp,rn) = positive' r d 
        (sb,sp,sn) = positive' s d
    in (rb&&sb,rp `intersect` sp, rn `intersect` sn)
positive' (Or r s) d = 
    let (rb,rp,rn) = positive' r d 
        (sb,sp,sn) = positive' s d
    in (rb&&sb,rp `intersect` sp, rn `intersect` sn)
positive' (Imp r s) d = 
    let (rb,rp,rn) = positive' r d 
        (sb,sp,sn) = positive' s d
    in (rb&&sb,rn `intersect` sp, rp `intersect` sn)
positive' (All x ty) d = 
    let (tyb,typ,tyn) = positive' ty (d+1)
    in (tyb,x:typ,x:tyn)
positive' (Mu x ty) d = 
    let (tyb,typ,tyn) = positive' ty (d+1)
    in (tyb && x `elem` typ)
-}

proofType = sequentType . proofSequent 
proofTerm = sequentTerm . proofSequent

makeProof :: MonadError String m => FunCtx -> VarCtx -> TypeCtx -> Term -> m PreProof
makeProof fctx ctx tctx (V v) = do
  ty <- maybeToError (varlookup v ctx) ("Failure to look up: "++ show v ++" in "++show ctx)
  return $ VarIntro (Holds fctx ctx tctx (V v) ty)
makeProof fctx ctx tctx (F f) = do
  ty <- maybeToError (ftypelookup f fctx) ("Failure to look up function symbol: "++f)
  return $ FunIntro (Holds fctx ctx tctx (F f) ty)
makeProof fctx ctx tctx Unit = return (UnitIntro (Holds fctx ctx tctx Unit One))
makeProof fctx ctx tctx (Pair t s) = do 
  d <- makeProof fctx ctx tctx t
  e <- makeProof fctx ctx tctx s
  return $ AndIntro (Holds fctx ctx tctx (Pair t s) (And (proofType d) (proofType e))) d e
makeProof fctx ctx tctx (Inl t (Or a b)) = do 
  d <- makeProof fctx ctx tctx t 
  let dty = proofType d
  if a == dty
    then return $ OrIntroL (Holds fctx ctx tctx (Inl t (Or a b)) (Or a b)) d
    else throwError $ "Incompatible types for left injection in "++show_term t ctx tctx
             ++"\n\tExpected: "++show_type a tctx++" and found: "++show_type dty tctx
makeProof fctx ctx tctx (Inr t (Or a b)) = do 
  d <- makeProof fctx ctx tctx t 
  let dty = proofType d
  if b == dty
    then return $ OrIntroR (Holds fctx ctx tctx (Inr t (Or a b)) (Or a b)) d
    else throwError $ "Incompatible types for right injection in "++show_term t ctx tctx
             ++"\n\tExpected: "++show_type b tctx++" and found: "++show_type dty tctx
makeProof fctx ctx tctx (Fold t (Mu x ty)) = do 
  d <- makeProof fctx ctx tctx t
  let dty = proofType d
  let unfolded = type_sub (Mu x ty) ty
  if dty == unfolded
    then return $ AlphaIntro (Holds fctx ctx tctx (Fold t (Mu x ty)) (Mu x ty)) d
    else throwError $ "Incompatible types for folding.  Found: "++show_type dty (x:tctx)++", expected: "++show_type dty tctx
makeProof fctx ctx tctx (Fold t (Nu x ty)) = do 
  d <- makeProof fctx ctx tctx t
  let dty = proofType d
  let unfolded = type_sub (Nu x ty) ty
  if dty == unfolded
    then return $ AlphaIntro (Holds fctx ctx tctx (Fold t (Nu x ty)) (Nu x ty)) d
    else throwError $ "Incompatible types for folding. Found: "++show_type dty (x:tctx)++", expected: "++show_type dty tctx
makeProof fctx ctx tctx (TLambda x t) = do 
  d <- makeProof fctx ctx (x:tctx) t
  let dty = proofType d
  return $ AllIntro (Holds fctx ctx tctx (TLambda x t) (All x dty)) d
makeProof fctx ctx tctx (Lambda x ty t) = do 
  d <- makeProof fctx ((x,ty):ctx) tctx t
  let dty = proofType d
  return $ ImpIntro (Holds fctx ctx tctx (Lambda x ty t) (Imp ty dty)) d
makeProof fctx ctx tctx (Split t x y s) = do 
  d <- makeProof fctx ctx tctx t 
  let dty = proofType d
  case dty of 
    And a b -> do 
             e <- makeProof fctx ((x,a):(y,b):ctx) tctx s
             let ety = proofType e
             return $ AndElim (Holds fctx ctx tctx (Split t x y s) ety) d e
    _ -> throwError $ "Incompatible type for split: "++show_type dty tctx
makeProof fctx ctx tctx (Case t x r y s) = do 
  d <- makeProof fctx ctx tctx t 
  let dty = proofType d
  case dty of 
    Or a b -> do 
             e <- makeProof fctx ((x,a):ctx) tctx r 
             f <- makeProof fctx ((y,b):ctx) tctx s
             let ety = proofType e
             let fty = proofType f
             if ety == fty 
               then return $ OrElim (Holds fctx ctx tctx (Case t x r y s) ety) d e f
               else throwError $ "Types don't match for case. Expected: "++show_type ety tctx++", found: "++show_type fty tctx
    _ -> throwError $ "Incompatible type for case: "++show_type dty tctx
makeProof fctx ctx tctx (App r s) = do 
  d <- makeProof fctx ctx tctx r
  e <- makeProof fctx ctx tctx s
  let dty = proofType d
  let ety = proofType e
  case dty of 
    Imp a b -> do 
             if a == ety
               then return $ ImpElim (Holds fctx ctx tctx (App r s) b) d e
               else throwError $ "Types don't match for application.  Expected:"++show_type a tctx++"\nfound:\n"++show_type ety tctx
                                    ++ " in "++ show (Holds fctx ctx tctx (App r s) b)
    _  -> throwError $ "Incompatible type in right term for application. \nExpected implication: \n"
           ++ show_type ety tctx++"\nfound:\n"++show_type dty tctx
           ++ " with term: \n"++show (Holds fctx ctx tctx (App r s) (FT "Unknown"))
makeProof fctx ctx tctx (Unfold t (Mu x ty)) = do 
  d <- makeProof fctx ctx tctx t 
  let dty = proofType d
  if dty == (Mu x ty)
    then return $ AlphaElim (Holds fctx ctx tctx (Unfold t (Mu x ty)) (type_sub (Mu x ty) ty)) d
    else throwError $ "Type is not a compatible mu type: "++show_type dty tctx
makeProof fctx ctx tctx (Unfold t (Nu x ty)) = do
  d <- makeProof fctx ctx tctx t
  let dty = proofType d 
  if dty == (Nu x ty)
    then return $ AlphaElim (Holds fctx ctx tctx (Unfold t (Nu x ty)) (type_sub (Nu x ty) ty)) d
    else throwError $ "Type is not a compatible mu type: "++show_type dty tctx
makeProof fctx ctx tctx (TApp t ty) = do
  d <- makeProof fctx ctx tctx t 
  let dty = proofType d
  case dty of 
    All v oty -> return $ AllElim (Holds fctx ctx tctx (TApp t ty) (type_sub ty oty)) d
    _ -> throwError $ "Left term not a type abstraction: "++show_type dty tctx++" in term "++show_term (TApp t ty) ctx tctx
makeProof fctx ctx tctx t = error ("WTF is: "++show (Holds fctx ctx tctx t One))

typeof :: MonadError String m => FunCtx -> VarCtx -> TypeCtx -> Term -> m Type
typeof fctx ctx tctx t = do 
  p <- makeProof fctx ctx tctx t
  return $ proofType p

holdsToProof :: MonadError String m => Holds -> m PreProof
holdsToProof h@(Holds fctx ctx tctx t ty) = do 
  p <- makeProof fctx ctx tctx t 
  if ty == proofType p 
    then return p 
    else throwError $ "Incompatible type with original sequent:" ++ show_type ty tctx

typeCheckFuns :: MonadError String m => FunCtx -> m ()
typeCheckFuns fctx = foldrM (\ (f,t,ty) _ -> do 
                               typeof fctx [] [] t `catchError` 
                                          (\ s -> throwError $ "In function "++f++" : "++show_type ty []++" = \n"
                                                  ++show_term t [] [] ++",\n"++s)
                               return ()) () fctx
