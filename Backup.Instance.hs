module Instance where 

import Lang 
import Utils
import Eval
--import Exceptions
import Data.Maybe 
--import Pretty 
import Data.List


type_instance :: Type -> Type -> Int -> [(Int,Type)] -> Maybe [(Int,Type)]
type_instance (TV i) (TV j) d env = if i == j
                                    then return env 
                                    else Nothing
type_instance One One d env = return env
type_instance (And a b) (And a' b') d env = do
  env' <- type_instance a a' d env
  type_instance b b' d env'
type_instance (Or a b) (Or a' b') d env = do 
  env' <- type_instance a a' d env
  type_instance b b' d env'
type_instance (Imp a b) (Imp a' b') d  env = do
  env' <- type_instance a a' d env
  type_instance b b' d env'
type_instance (Nu x a) (Nu x' a') d env = do
  type_instance a a' (d+1) env
type_instance (Mu x a) (Mu x' a') d env = do 
  type_instance a a' (d+1) env
type_instance (All x a) (All x' a') d env = do 
  type_instance a a' (d+1) env
type_instance (TV i) ty d env =
    if i < d 
    then Nothing
    else case lookup i env of 
           Nothing -> return $ (i,ty):env
           Just a -> if a == ty
                     then return $ env
                     else Nothing
type_instance ty1 ty2 d env = Nothing

-- >- 
(>-) :: Holds -> Holds -> Maybe [(Int,Term)]
(>-) (fctx,ctx,tctx,t,ty) (fctx',ctx',tctx',t',ty') = 
    if ty == ty'
    then (do 
             inst t t' ctx (length ctx) []
             tysub <- type_instance ty ty' (length tctx) [] 
             let (vars,types) = unzip tysub
             let tsubed = type_sub_term types vars t (length tctx)
             inst t t' ctx (length ctx) [])
    else fail


inst ::  Holds -> Holds -> [(Int,Ty)] -> [(Int,Term)] -> Maybe [(Int,Term)]
inst (V i) (V j) env = 
    if i == j 
    then return env 
    else Nothing
inst (F f) (F g) ctx d env = 
    if f == g
    then return env 
    else Nothing
inst (Inl t ty) (Inl t' ty') ctx d env = do 
  inst t t' d ctx env 
inst (Inr t ty) (Inr t' ty') d ctx env = do 
  inst t t' d ctx env 
inst (Fold t ty) (Fold t' ty') d ctx env = do 
  inst t t' d ctx env
inst (Pair t s) (Pair t' s') d ctx env = do 
  env' <- inst t t' d ctx env
  inst s s' d ctx env'
inst (Lambda x ty t) (Lambda x' ty' t') d ctx env = do 
  inst t t' (d+1) env
inst (TLambda x t) (TLambda x' t') d ctx env = do
  inst t t' d ctx env
inst (Case t x r y s) (Case t' x' r' y' s') d ctx env = do 
  env' <- inst t t' d ctx env
  env'' <- inst r r' (d+1) env'
  inst s s' (d+1) env''
inst (Split t x y r) (Split t' x' y' r') d ctx env = do 
  env' <- inst t t' d ctx env 
  inst r r' (d+2) env'
inst (Unfold t ty) (Unfold t' ty') d ctx env = do 
  inst t t' d ctx env 
inst (App r s) (App r' s') d ctx env = do 
  env' <- inst r r' d ctx env 
  inst s s' d ctx env'
inst (TApp t ty) (TApp t' ty') d ctx env = do 
  inst t t' d ctx env 
inst (V i) t d ctx env =
  if lookup i env == t 
  then return env 
  else if i > d && all (>d) (freevars t)
       then return $ (i,t):env 
       else fail
