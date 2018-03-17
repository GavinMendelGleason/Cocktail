module Normalise where

import Lang
import Eval
import Data.List 
import Frame 
import Utils
import Data.Foldable (foldrM) 
import Data.Maybe
import Control.Monad.Identity 
import Debug.Trace
import Derivation 
import Pretty
import Control.Monad.Error

-- rewrite performs an equational rewrite as justified by information propagation.
rewrite :: Term -> Term -> Term -> Term
rewrite s t u | s == u = t
rewrite s t (V i) = V i
rewrite s t (F f) = F f
rewrite s t Unit = Unit
rewrite s t (Inl u ty) = Inl (rewrite s t u) ty
rewrite s t (Inr u ty) = Inr (rewrite s t u) ty
rewrite s t (Pair u v) = Pair (rewrite s t u) (rewrite s t v)
rewrite s t (Fold u ty) = Fold (rewrite s t u) ty
rewrite s t (Lambda x ty u) = Lambda x ty (rewrite (shift s 0 1) (shift t 0 1) u)
rewrite s t (TLambda x u) = TLambda x (rewrite s t u)
rewrite s t (Unfold u ty) = Unfold (rewrite s t u) ty
rewrite s t (App u v) = App (rewrite s t u) (rewrite s t v)
rewrite s t (TApp u ty) = TApp (rewrite s t u) ty
rewrite s t (Case u x v y w) = Case (rewrite s t u) x (rewrite (shift s 0 1) (shift t 0 1) v) y (rewrite (shift s 0 1) (shift t 0 1) w)
rewrite s t (Split u x y v) = Split (rewrite s t u) x y (rewrite (shift s 0 2) (shift t 0 2) v)

sequentNorm :: Holds -> Holds 
sequentNorm (Holds fctx vctx tctx t ty) = Holds fctx vctx tctx (norm fctx t) ty

norm :: FunCtx -> Term -> Term
norm fctx (V v) = V v
norm fctx (F f) = if recursivep (F f) fctx
                    then (F f)
                    else case (ftermlookup f fctx) of
                           Nothing -> (F f)
                           Just t -> norm fctx t
norm fctx Unit = Unit
norm fctx (Inl t ty) = Inl (norm fctx t) ty
norm fctx (Inr t ty) = Inr (norm fctx t) ty
norm fctx (Pair t s) = Pair (norm fctx t) (norm fctx s)
norm fctx (Fold t ty) = Fold (norm fctx t) ty
norm fctx (Lambda x ty t) = Lambda x ty (norm fctx t)
norm fctx (TLambda x t) = TLambda x t 
norm fctx (Unfold (Fold t _) _) = norm fctx t
norm fctx (Unfold (Case t x r y s) ty) = norm fctx (Case t x (Unfold r ty) y (Unfold s ty))
norm fctx (Unfold (Split t x y s) ty) = norm fctx (Split t x y (Unfold s ty))
norm fctx (Unfold t ty) = if irred t 
                     then Unfold t ty 
                     else norm fctx (Unfold (norm fctx t) ty)
norm fctx (App (Lambda _ _ t) s) = norm fctx (sub s t)
norm fctx (App r s) = if irred r 
                 then (App r s) 
                 else norm fctx (App (norm fctx r) s)
norm fctx (TApp (TLambda _ t) ty) = norm fctx (type_sub_term ty t)
norm fctx (TApp t ty) = if irred t 
                   then (TApp t ty) 
                   else norm fctx (TApp (norm fctx t) ty)
norm fctx (Case (Inl t _) _ s _ r) = norm fctx (sub t s)
norm fctx (Case (Inr t _) _ s _ r) = norm fctx (sub t r)
norm fctx (Case (Case t x r y s) v a w b) = norm fctx (Case t 
                                             x (Case r v (shift a 1 1) w (shift b 1 1)) 
                                             y (Case s v (shift a 1 1) w (shift b 1 1)))
norm fctx (Case (Split t x y s) v a w b) = norm fctx (Split t x y 
                                            (Case s 
                                             v (shift a 1 2)
                                             w (shift b 1 2)))
norm fctx (Case t x s y r) = if irred t 
                        then (Case t x (norm fctx s) y (norm fctx r))
                        else norm fctx (Case (norm fctx t) x (norm fctx s) y (norm fctx r))
norm fctx (Split (Pair s t) _ _ r) = norm fctx (sub' [s,t] [0,1] r 0 2)
norm fctx (Split (Split t x y r) v w u) = norm fctx (Split t x y 
                                           (Split r v w (shift u 2 2)))
norm fctx (Split (Case t x r y s) v w u) = norm fctx (Case t 
                                            x (Split r v w (shift u 2 1))
                                            y (Split s v w (shift u 2 1)))
norm fctx (Split t x y r) = if irred t
                       then Split t x y (norm fctx r)
                       else norm fctx (Split (norm fctx t) x y (norm fctx r))

propogateSequent :: MonadError String m => Holds -> m Holds
propogateSequent (Holds fctx vctx tctx t ty) = do 
  t' <- propogate fctx vctx tctx t 
  return $ Holds fctx vctx tctx t' ty

propogate :: MonadError String m => FunCtx -> VarCtx -> TypeCtx -> Term -> m Term
propogate fctx vctx tctx (V i) = return $ V i
propogate fctx vctx tctx (F f) = return $ F f
propogate fctx vctx tctx Unit = return $ Unit
propogate fctx vctx tctx (Inl u ty) = do 
  u' <- propogate fctx vctx tctx u
  return $ Inl u' ty
propogate fctx vctx tctx (Inr u ty) = do 
  u' <- propogate fctx vctx tctx u
  return $ Inr u' ty
propogate fctx vctx tctx (Pair u v) = do 
  u' <- propogate fctx vctx tctx u
  v' <- propogate fctx vctx tctx v
  return $ Pair u' v'
propogate fctx vctx tctx (Fold u ty) = do 
  u' <- propogate fctx vctx tctx u
  return $ Fold u' ty
propogate fctx vctx tctx (Lambda x ty u) = do 
  u' <- propogate fctx ((x,ty):vctx) tctx u
  return $ Lambda x ty u'
propogate fctx vctx tctx (TLambda x u) = do 
  u' <- propogate fctx vctx (x:tctx) u 
  return $ TLambda x u'
propogate fctx vctx tctx (Unfold u ty) = do 
  u' <- propogate fctx vctx tctx u 
  return $ Unfold u' ty
propogate fctx vctx tctx (App u v) = do 
  u' <- propogate fctx vctx tctx u
  v' <- propogate fctx vctx tctx v
  return $ App u' v'
propogate fctx vctx tctx (TApp u ty) = do 
  u' <- propogate fctx vctx tctx u 
  return $ TApp u' ty
propogate fctx vctx tctx (Case (Unfold u ty) x v y w) = do
  uty <- typeof fctx vctx tctx (Unfold u ty)
  case uty of 
    Or tya tyb -> do
             u' <- propogate fctx vctx tctx (norm fctx u)
             let s = shift u' 0 1
             let v' = rewrite s (Fold (Inl (V 0) uty) ty) v
             let w' = rewrite s (Fold (Inr (V 0) uty) ty) w
             v'' <- propogate fctx ((x,tya):vctx) tctx v' 
             w'' <- propogate fctx ((y,tyb):vctx) tctx w'
             return $ Case (Unfold u' ty) x v'' y w''
    _ -> throwError $ "Invalid type for case: "++show_type uty tctx
propogate fctx vctx tctx (Case u x v y w) = do
  uty <- typeof fctx vctx tctx u
  case uty of 
    Or tya tyb -> do
             u' <- propogate fctx vctx tctx (norm fctx u)
             let s = shift u' 0 1
             let v' = rewrite s (Inl (V 0) uty) v
             let w' = rewrite s (Inr (V 0) uty) w
             v'' <- propogate fctx ((x,tya):vctx) tctx v' 
             w'' <- propogate fctx ((y,tyb):vctx) tctx w'
             return $ Case u' x v'' y w''
    _ -> throwError $ "Invalid type for case: "++show_type uty tctx
propogate fctx vctx tctx (Split (Unfold u ty) x y v) = do
  uty <- typeof fctx vctx tctx (Unfold u ty)
  case uty of 
    And tya tyb -> do
             u' <- propogate fctx vctx tctx (norm fctx u)
             let s = shift u' 0 2 
             let v' = rewrite s (Fold (Pair (V 0) (V 1)) ty) v
             v'' <- propogate fctx ((x,tya):(y,tyb):vctx) tctx v' 
             return $ Split (Unfold u' ty) x y v''
    _ -> throwError $ "Invalid type for split: "++show_type uty tctx
propogate fctx vctx tctx (Split u x y v) = do
  uty <- typeof fctx vctx tctx u
  case uty of 
    And tya tyb -> do
             u' <- propogate fctx vctx tctx (norm fctx u)
             let s = shift u' 0 2 
             let v' = rewrite s (Pair (V 0) (V 1)) v
             v'' <- propogate fctx ((x,tya):(y,tyb):vctx) tctx v' 
             return $ Split u' x y v''
    _ -> throwError $ "Invalid type for split: "++show_type uty tctx

{- Because we do not use weakening laws, terms may have gaps between
   free variables strengthenTerm essentialy "strengthens" the context
   so that all variables are ordred starting from zero.  This
   simplifies abstracting over a context to produce a function term
   which does not have useless arguments.

   The input list must be the list of all free variables. -}

strengthenTerm :: [Int] -> [Int] -> Term -> Term
strengthenTerm vl tvl t = runIdentity $ strengthenTerm' vl tvl 0 0 t 
                       
strengthenType :: [Int] -> Type -> Type
strengthenType tvl ty = runIdentity $ strengthenType' tvl 0 ty
   
strengthenType' :: [Int] -> Int -> Type -> M Type
strengthenType' tvl tlb One = return One
strengthenType' tvl tlb (TV i) = if i < tlb
                                 then return (TV i)
                                 else case findIndex (==i-tlb) tvl of 
                                        Just j -> return $ TV (j+tlb)
                                        Nothing -> return $ TV i
strengthenType' tvl tlb (And ty1 ty2) = do 
  ty1' <- strengthenType' tvl tlb ty1
  ty2' <- strengthenType' tvl tlb ty2
  return (And ty1' ty2')
strengthenType' tvl tlb (Or ty1 ty2) = do 
  ty1' <- strengthenType' tvl tlb ty1
  ty2' <- strengthenType' tvl tlb ty2
  return (Or ty1' ty2')
strengthenType' tvl tlb (Imp ty1 ty2) = do 
  ty1' <- strengthenType' tvl tlb ty1
  ty2' <- strengthenType' tvl tlb ty2
  return (Imp ty1' ty2')
strengthenType' tvl tlb (All x ty) = do 
  ty' <- strengthenType' tvl (tlb+1) ty
  return (All x ty')
strengthenType' tvl tlb (Mu x ty) = do 
  ty' <- strengthenType' tvl (tlb+1) ty
  return (Mu x ty')
strengthenType' tvl tlb (Nu x ty) = do 
  ty' <- strengthenType' tvl (tlb+1) ty
  return (Nu x ty')

strengthenTerm' :: [Int] -> [Int] -> Int -> Int -> Term -> M Term
strengthenTerm' vl tvl lb tlb (V i) = if i < lb
                                      then return $ V i
                                      else case findIndex (==i-lb) vl of 
                                             Just j -> return $ V (j+lb)
                                             Nothing -> return $ V i
strengthenTerm' vl tvl lb tlb (F f) = return (F f) 
strengthenTerm' vl tvl lb tlb Unit = return Unit
strengthenTerm' vl tvl lb tlb (App t s) = do 
  t' <- strengthenTerm' vl tvl lb tlb t 
  s' <- strengthenTerm' vl tvl lb tlb s 
  return (App t' s') 
strengthenTerm' vl tvl lb tlb (TApp t ty) = do 
  t' <- strengthenTerm' vl tvl lb tlb t
  ty' <- strengthenType' tvl tlb ty
  return (TApp t' ty') 
strengthenTerm' vl tvl lb tlb (Pair t s) = do
  t' <- strengthenTerm' vl tvl lb tlb t 
  s' <- strengthenTerm' vl tvl lb tlb s 
  return (Pair t' s')
strengthenTerm' vl tvl lb tlb (Inl t ty) = do
  t' <- strengthenTerm' vl tvl lb tlb t 
  ty' <- strengthenType' tvl tlb ty
  return (Inl t' ty')
strengthenTerm' vl tvl lb tlb (Inr t ty) = do
  t' <- strengthenTerm' vl tvl lb tlb t 
  ty' <- strengthenType' tvl tlb ty
  return (Inr t' ty')
strengthenTerm' vl tvl lb tlb (Fold t ty) = do
  t' <- strengthenTerm' vl tvl lb tlb t 
  ty' <- strengthenType' tvl tlb ty
  return (Fold t' ty')
strengthenTerm' vl tvl lb tlb (Unfold t ty) = do
  t' <- strengthenTerm' vl tvl lb tlb t 
  ty' <- strengthenType' tvl tlb ty
  return (Unfold t' ty')
strengthenTerm' vl tvl lb tlb (Case t x r y s) = do 
  t' <- strengthenTerm' vl tvl lb tlb t 
  r' <- strengthenTerm' vl tvl (lb+1) tlb r
  s' <- strengthenTerm' vl tvl (lb+1) tlb s 
  return (Case t' x r' y s')
strengthenTerm' vl tvl lb tlb (Split t x y s) = do 
  t' <- strengthenTerm' vl tvl lb tlb t 
  s' <- strengthenTerm' vl tvl (lb+2) tlb s 
  return (Split t' x y s')
strengthenTerm' vl tvl lb tlb (Lambda x ty t) = do 
  t' <- strengthenTerm' vl tvl (lb+1) tlb t 
  ty' <- strengthenType' tvl tlb ty
  return (Lambda x ty' t')
strengthenTerm' vl tvl lb tlb (TLambda x t) = do 
  t' <- strengthenTerm' vl tvl lb (tlb+1) t 
  return (TLambda x t')

strengthen h@(Holds fctx vctx tctx t ty) = do
  let (ftvs,fvs) = freevars vctx t
      strongt = strengthenTerm fvs ftvs t
      strongty = strengthenType ftvs ty
  vctx' <- foldrM (\ i r -> do 
                     (v,ty) <- ith i vctx
                     let ty' = strengthenType ftvs ty
                     return ((v,ty'):r)) [] fvs
  tctx' <- foldrM (\ i r -> do 
                     tyn <- ith i tctx
                     return (tyn:r)) [] ftvs
  return (Holds fctx vctx' tctx' strongt strongty)
