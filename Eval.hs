module Eval where

import Lang
import Data.List 
import Utils
import Data.Maybe
import Control.Monad.Identity 

type M = Identity

type_shift' :: Type -> Int -> Int -> Type
-- k is a cutoff 
-- d is the number of times we need to lift it.
type_shift' One k d = One
type_shift' (TV j) k d = if k <= j 
                         then TV (j+d) 
                         else TV j
type_shift' (And tya tyb) k d = And (type_shift' tya k d) (type_shift' tyb k d) 
type_shift' (Or tya tyb) k d = Or (type_shift' tya k d) (type_shift' tyb k d) 
type_shift' (Imp tya tyb) k d = Imp (type_shift' tya k d) (type_shift' tyb k d) 
type_shift' (All n tya) k d = All n (type_shift' tya (k+1) d) 
type_shift' (Nu x tya) k d = Nu x (type_shift' tya (k+1) d)
type_shift' (Mu x tya) k d = Mu x (type_shift' tya (k+1) d)

type_shift :: Type -> Int -> Type
type_shift ty d = type_shift' ty 0 d 

-- implement simultaneous substitution
type_sub' :: [Type] -> [Int] -> Int -> Type -> Int -> Type
-- tys: are the substituted types
-- ds: are the free variables we need to substitute for
-- lb: is the number of TLambda binders encountered
-- n: number of lambda binders being stripped (lowering)
type_sub' tys ds lb One n = One
type_sub' tys ds lb (TV j) n = case elemIndex (j-lb) ds of 
                                 Nothing -> if j > lb 
                                            then TV (j-n) 
                                            else TV j 
                                 Just i -> type_shift (tys!!i) lb
type_sub' tys ds lb (And tya tyb) n = 
    let tya' = type_sub' tys ds lb tya n
        tyb' = type_sub' tys ds lb tyb n
    in And tya' tyb'
type_sub' tys ds lb (Or tya tyb) n =
    let tya' = type_sub' tys ds lb tya n
        tyb' = type_sub' tys ds lb tyb n
    in Or tya' tyb'
type_sub' tys ds lb (Imp tya tyb) n =
    let tya' = type_sub' tys ds lb tya n
        tyb' = type_sub' tys ds lb tyb n
    in Imp tya' tyb'
type_sub' tys ds lb (All x tya) n =
    let tya' = type_sub' tys ds (1+lb) tya n
    in (All x tya')
type_sub' tys ds lb (Nu x tya) n =
    let tya' = type_sub' tys ds (1+lb) tya n
    in (Nu x tya')
type_sub' tys ds lb (Mu x tya) n =
    let tya' = type_sub' tys ds (1+lb) tya n
    in (Mu x tya')

type_sub ty tyo = type_sub' [ty] [0] 0 tyo 1

shift :: Term -> Int -> Int -> Term
-- k is the cuttoff 
-- n is the amount to shift' by
shift (V i) k n = if k <= i 
                  then V (i+n)
                  else V i
shift Unit k n = Unit
shift (F f) k n = F f
shift (App t s) k n = App (shift t k n) (shift s k n)
shift (TApp t ty) k n = TApp (shift t k n) ty
shift (Lambda x ty t) k n = Lambda x ty (shift t (k+1) n)
shift (TLambda x t) k n = TLambda x (shift t k n)
shift (Unfold t ty) k n = Unfold (shift t k n) ty
shift (Fold t ty) k n = Fold (shift t k n) ty
shift (Inl t ty) k n = Inl (shift t k n) ty
shift (Inr t ty) k n = Inr (shift t k n) ty
shift (Pair t s) k n = Pair (shift t k n) (shift s k n)
shift (Case t x r y s) k n = Case (shift t k n) x (shift r (k+1) n) y (shift s (k+1) n)
shift (Split t x y r) k n = Split (shift t k n) x y (shift r (k+2) n) 



-- simultaneous substitution
sub' :: [Term] -> [Int] -> Term -> Int -> Int -> Term
-- ts: terms to substitute
-- is: freevariables in need of subsitution
-- lb: number of lambda binders 
-- n: number of lambda binders stripped from the original term to shift free vars by.
sub' ts is (V j) lb n = case elemIndex (j-lb) is of 
                          Nothing ->
                              -- Free variable 
                              if j > lb 
                              then V (j-n)
                              else V j 
                          Just i -> shift (ts!!i) 0 lb
sub' ts is (F f) lb n = F f
sub' ts is Unit lb n = Unit
sub' ts is (App r s) lb n = App (sub' ts is r lb n) (sub' ts is s lb n)
sub' ts is (TApp r ty) lb n = TApp (sub' ts is r lb n) ty
sub' ts is (Lambda x ty s) lb n = Lambda x ty (sub' ts is s (1+lb) n)
sub' ts is (TLambda x s) lb n = TLambda x (sub' ts is s lb n)
sub' ts is (Case t x r y s) lb n = Case (sub' ts is t lb n) x (sub' ts is r (lb+1) n) y (sub' ts is s (lb+1) n)
sub' ts is (Split t x y r) lb n = Split (sub' ts is t lb n) x y (sub' ts is r (lb+2) n)
sub' ts is (Inr t ty) lb n = Inr (sub' ts is t lb n) ty
sub' ts is (Inl t ty) lb n = Inl (sub' ts is t lb n) ty 
sub' ts is (Unfold t ty) lb n = Unfold (sub' ts is t lb n) ty 
sub' ts is (Fold t ty) lb n = Fold (sub' ts is t lb n) ty 
sub' ts is (Pair t r) lb n = Pair (sub' ts is t lb n) (sub' ts is r lb n)

sub :: Term -> Term -> Term
sub t o = sub' [t] [0] o 0 1

type_sub_term' :: [Type] -> [Int] -> Term -> Int -> Int -> Term 
-- ts: types being substituted 
-- is: type variables being replaced
-- lb: number of lambda binders 
-- n: number of lambda binders stripped to lower free vars by
type_sub_term' ts is (V j) lb n = (V j)
type_sub_term' ts is (F f) lb n = F f
type_sub_term' ts is Unit lb n = Unit
type_sub_term' ts is (App r s) lb n = App (type_sub_term' ts is r lb n) 
                                        (type_sub_term' ts is s lb n)
type_sub_term' ts is (TApp r ty) lb n = TApp (type_sub_term' ts is r lb n) 
                                          (type_sub' ts is lb ty n)
type_sub_term' ts is (Lambda x ty s) lb n = Lambda x (type_sub' ts is lb ty n) 
                                              (type_sub_term' ts is s lb n)
type_sub_term' ts is (TLambda x s) lb n = TLambda x (type_sub_term' ts is s (lb+1) n)
type_sub_term' ts is (Case t x r y s) lb n = Case (type_sub_term' ts is t lb n) 
                                             x (type_sub_term' ts is r lb n)
                                             y (type_sub_term' ts is s lb n)
type_sub_term' ts is (Split t x y r) lb n = Split (type_sub_term' ts is t lb n) 
                                            x y (type_sub_term' ts is r lb n)
type_sub_term' ts is (Inr t ty) lb n = Inr (type_sub_term' ts is t lb n) (type_sub' ts is lb ty n)
type_sub_term' ts is (Inl t ty) lb n = Inl (type_sub_term' ts is t lb n) (type_sub' ts is lb ty n)
type_sub_term' ts is (Unfold t ty) lb n = Unfold (type_sub_term' ts is t lb n) (type_sub' ts is lb ty n)
type_sub_term' ts is (Fold t ty) lb n = Fold (type_sub_term' ts is t lb n) (type_sub' ts is lb ty n) 
type_sub_term' ts is (Pair t s) lb n = Pair (type_sub_term' ts is t lb n) (type_sub_term' ts is s lb n)

type_sub_term :: Type -> Term -> Term
type_sub_term ty t = type_sub_term' [ty] [0] t 0 1

{-
implement eval for closed terms

eval 
-}

freeTypeVars tyi One = [] 
freeTypeVars tyi (TV i) = if i >= tyi
                           then [i-tyi]
                           else []
freeTypeVars tyi (And s t) = (freeTypeVars tyi s) ++ (freeTypeVars tyi t)
freeTypeVars tyi (Or s t) = (freeTypeVars tyi s) ++ (freeTypeVars tyi t) 
freeTypeVars tyi (Imp s t) = (freeTypeVars tyi s) ++ (freeTypeVars tyi t) 
freeTypeVars tyi (All n t) = freeTypeVars (tyi+1) t
freeTypeVars tyi (Nu n t) = freeTypeVars (tyi+1) t
freeTypeVars tyi (Mu n t) = freeTypeVars (tyi+1) t

freevars :: VarCtx -> Term -> ([TVar],[Var])
freevars vctx t = let (tv,v) = freevars' 0 0 t 
                      tv' = concatMap (\ i -> concatMap (freeTypeVars 0) $ maybeToList $ fmap snd $ ith i vctx) v
                      tv'' = sort (nub (tv++tv'))
                      v' = sort (nub v)
                  in (tv'',v')

freevars' tyi ti Unit = ([],[]) 
freevars' tyi ti (V i) = if i >= ti
                         then ([],[i-ti]) 
                         else ([],[])
freevars' tyi ti (F _) = ([],[]) 
freevars' tyi ti (App t s) = let (ty1,v1) = freevars' tyi ti t 
                                 (ty2,v2) = freevars' tyi ti s
                             in (ty1++ty2,v1++v2)
freevars' tyi ti (TApp t ty) = let (ty1,v1) = freevars' tyi ti t 
                                   ty2 = freeTypeVars tyi ty 
                               in (ty1++ty2,v1)
freevars' tyi ti (Pair t s) = let (ty1,v1) = freevars' tyi ti t 
                                  (ty2,v2) = freevars' tyi ti s
                              in  (ty1++ty2,v1++v2)
freevars' tyi ti (Inl t ty) = let (ty1,v1) = freevars' tyi ti t 
                                  ty2 = freeTypeVars tyi ty 
                              in (ty1++ty2,v1)
freevars' tyi ti (Inr t ty) = let (ty1,v1) = freevars' tyi ti t 
                                  ty2 = freeTypeVars tyi ty 
                              in (ty1++ty2,v1)
freevars' tyi ti (Fold t ty) = let (ty1,v1) = freevars' tyi ti t 
                                   ty2 = freeTypeVars tyi ty 
                               in (ty1++ty2,v1)
freevars' tyi ti (Unfold t ty) = let (ty1,v1) = freevars' tyi ti t 
                                     ty2 = freeTypeVars tyi ty 
                                 in (ty1++ty2,v1)
freevars' tyi ti (Case t x r y s) = let (ty1,v1) = freevars' tyi ti t
                                        (ty2,v2) = freevars' tyi (1+ti) r
                                        (ty3,v3) = freevars' tyi (1+ti) s
                                    in (ty1++ty2++ty3,v1++v2++v3)
freevars' tyi ti (Split t x y s) = let (ty1,v1) = freevars' tyi ti t
                                       (ty2,v2) = freevars' tyi (2+ti) s
                                   in (ty1++ty2,v1++v2)
freevars' tyi ti (Lambda x ty t) = let (ty1,v1) = freevars' tyi (1+ti) t
                                       ty2 = freeTypeVars tyi ty
                                   in (ty1++ty2,v1)
freevars' tyi ti (TLambda x t) = freevars' (1+tyi) ti t

boundvars :: Int -> Int -> VarCtx -> Term -> ([TVar],[Var])
boundvars lb tlb vctx t = let (tyvs,tvs) = freevars vctx t
                              tyvs' = filter (<tlb) tyvs 
                              tvs' = filter (<lb) tvs                                     
                          in (tyvs',tvs')
