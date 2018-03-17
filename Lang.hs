module Lang where

import Data.List 
import Utils 
import Debug.Trace

type Var = Int 
type TVar = Int
type Name = String
type Fun = String
data Type = One 
          | TV TVar
          | FT Name
          | And Type Type 
          | Or Type Type 
          | Imp Type Type
          | All Name Type 
          | Mu Name Type
          | Nu Name Type 

instance Eq Type where 
    (==) One One = True 
    (==) (TV i) (TV j) = i == j
    (==) (And s t) (And u v) = s == u && t == v
    (==) (Or s t) (Or u v) =  s == u && t == v
    (==) (Imp s t) (Imp u v) = s == u && t == v
    (==) (All _ t) (All _ s) = t == s
    (==) (Nu _ t) (Nu _ s) = t == s
    (==) (Mu _ t) (Mu _ s) = t == s
    (==) _ _ = False

data Term = V Var
          | F Fun
          | Unit
          | App Term Term
          | TApp Term Type
          | Pair Term Term
          | Inl Term Type
          | Inr Term Type
          | Fold Term Type 
          | Unfold Term Type
          | Case Term Name Term Name Term 
          | Split Term Name Name Term
          | Lambda Name Type Term 
          | TLambda Name Term 
          | Ev Term Term

instance Eq Term where 
    (==) (V i) (V j) = i == j 
    (==) (F f) (F g) = f == g 
    (==) Unit Unit = True
    (==) (App f t) (App g s) = f == g && t == s
    (==) (TApp t ty1) (TApp s ty2) = t == s && ty1 == ty2 
    (==) (Pair a b) (Pair c d) = a == c && b == d
    (==) (Inl a ty1) (Inl b ty2) = a == b && ty1 == ty2 
    (==) (Inr a ty1) (Inr b ty2) = a == b && ty1 == ty2 
    (==) (Fold a ty1) (Fold b ty2) = a == b && ty1 == ty2 
    (==) (Unfold a ty1) (Unfold b ty2) = a == b && ty1 == ty2
    (==) (Case t1 _ s1 _ r1) (Case t2 _ s2 _ r2) = 
         t1 == t2 && s1 == s2 && r1 == r2
    (==) (Split t1 _ _ s1) (Split t2 _ _ s2) = t1 == t2 && s1 == s2
    (==) (Lambda _ ty1 t1) (Lambda _ ty2 t2) = ty1 == ty2 && t1 == t2
    (==) (TLambda _ t1) (TLambda _ t2) = t1 == t2
    (==) (Ev t t') s = t == s || t' == s
    (==) t (Ev s s') = t == s || t == s'
    (==) _ _ = False

type TypeCtx = [Name] 
type VarCtx = [(Name,Type)]
type Recursive = Bool
type FunCtx = [(Name,Term,Type)] 
data Holds = Holds FunCtx VarCtx TypeCtx Term Type

ftypelookup :: Name -> FunCtx -> Maybe Type
ftypelookup n [] = Nothing
ftypelookup n ((m,_,ty):t) = if n == m 
                             then Just ty 
                             else ftypelookup n t
ftermlookup :: Name -> FunCtx -> Maybe Term
ftermlookup n [] = Nothing
ftermlookup n ((m,term,_):t) = if n == m 
                               then Just term 
                               else ftermlookup n t

varlookup :: Int -> VarCtx -> Maybe Type
varlookup n xs = fmap snd (ith n xs)

abstract vl lb (F f) = case findIndex (==f) vl of 
                      Nothing -> F f
                      Just i -> V (i+lb)
abstract vl lb (V i) = V i
abstract vl lb Unit = Unit
abstract vl lb (App t s) = App (abstract vl lb t) (abstract vl lb s)
abstract vl lb (TApp t ty) = TApp (abstract vl lb t) ty
abstract vl lb (Pair t s) = Pair (abstract vl lb t) (abstract vl lb s)
abstract vl lb (Inl t ty) = Inl (abstract vl lb t) ty
abstract vl lb (Inr t ty) = Inr (abstract vl lb t) ty
abstract vl lb (Fold t ty) = Fold (abstract vl lb t) ty
abstract vl lb (Unfold t ty) = Unfold (abstract vl lb t) ty
abstract vl lb (Case t x r y s) = Case (abstract vl lb t) x (abstract (delete x vl) (1+lb) r) y (abstract (delete y vl) (1+lb) s)
abstract vl lb (Split t x y s) = Split (abstract vl lb t) x y (abstract (delete x (delete y vl)) (2+lb) s)
abstract vl lb (Lambda x ty t) = Lambda x ty (abstract vl lb t)
abstract vl lb (TLambda x t) = TLambda x (abstract (delete x vl) (lb+1) t)

abstractType :: [Name] -> Int -> Type -> Type
abstractType vl lb One = One
abstractType vl lb (TV i) = TV i
abstractType vl lb (FT f) = case findIndex (==f) vl of
                              Nothing -> FT f 
                              Just i -> TV (i+lb) 
abstractType vl lb (And ty1 ty2) = And (abstractType vl lb ty1) (abstractType vl lb ty2) 
abstractType vl lb (Or ty1 ty2) = Or (abstractType vl lb ty1) (abstractType vl lb ty2) 
abstractType vl lb (Imp ty1 ty2) = Imp (abstractType vl lb ty1) (abstractType vl lb ty2) 
abstractType vl lb (All x ty) = All x (abstractType (delete x vl) (1+lb) ty) 
abstractType vl lb (Mu x ty) = Mu x (abstractType (delete x vl) (1+lb) ty) 
abstractType vl lb (Nu x ty) = Nu x (abstractType (delete x vl) (1+lb) ty) 

abstractTypeTerm vl lb (F f) = F f
abstractTypeTerm vl lb (V i) = V i
abstractTypeTerm vl lb Unit = Unit
abstractTypeTerm vl lb (App t s) = App (abstractTypeTerm vl lb t) (abstractTypeTerm vl lb s)
abstractTypeTerm vl lb (TApp t ty) = TApp (abstractTypeTerm vl lb t) (abstractType vl lb ty)
abstractTypeTerm vl lb (Pair t s) = Pair (abstractTypeTerm vl lb t) (abstractTypeTerm vl lb s)
abstractTypeTerm vl lb (Inl t ty) = Inl (abstractTypeTerm vl lb t) (abstractType vl lb ty)
abstractTypeTerm vl lb (Inr t ty) = Inr (abstractTypeTerm vl lb t) (abstractType vl lb ty)
abstractTypeTerm vl lb (Fold t ty) = Fold (abstractTypeTerm vl lb t) (abstractType vl lb ty)
abstractTypeTerm vl lb (Unfold t ty) = Unfold (abstractTypeTerm vl lb t) (abstractType vl lb ty)
abstractTypeTerm vl lb (Case t x r y s) = Case (abstractTypeTerm vl lb t) x (abstractTypeTerm vl lb r) y (abstractTypeTerm vl lb s)
abstractTypeTerm vl lb (Split t x y s) = Split (abstractTypeTerm vl lb t) x y (abstractTypeTerm vl lb s)
abstractTypeTerm vl lb (Lambda x ty t) = Lambda x (abstractType vl lb ty) (abstractTypeTerm vl lb t)
abstractTypeTerm vl lb (TLambda x t) = TLambda x (abstractTypeTerm (delete x vl) (1+lb) t)

makeLam vlty t = let vl = map fst vlty 
                     t' = abstract (reverse vl) 0 t                      
                 in foldr (\ (v,ty) r -> Lambda v ty r) t' vlty

makeTLam vl t = let t' = abstractTypeTerm (reverse vl) 0 t
                in foldr (\ v r -> TLambda v r) t' vl

makeCase t x l y r = let l' = abstract [x] 0 l
                         r' = abstract [y] 0 r
                     in Case t x l' y r'

makeSplit t x y r = let r' = abstract [x,y] 0 r 
                    in Split t x y r'

makeAll vl t = let t' = abstractType (reverse vl) 0 t
               in foldr (\ v r -> All v r) t' vl

makeMu vl t = let t' = abstractType (reverse vl) 0 t
              in foldr (\ v r -> Mu v r) t' vl

makeNu vl t = let t' = abstractType (reverse vl) 0 t
              in foldr (\ v r -> Nu v r) t' vl

freshen v vars = freshen' v v vars 0
freshen' origv v vars i  = case find (==v) vars of 
                             Nothing -> v 
                             Just _ -> freshen' origv (origv++show i) vars (i+1)

recursivep t fctx = recursivep' t fctx []

recursivep' (V v) fctx seen = False
recursivep' (F f) fctx seen = if f `elem` seen 
                                then True
                                else case (ftermlookup f fctx) of 
                                        Nothing -> False
                                        Just t -> recursivep' t fctx (f:seen)
recursivep' Unit fctx seen = False
recursivep' (App t s) fctx seen = recursivep' t fctx seen && recursivep' s fctx seen
recursivep' (TApp t _) fctx seen = recursivep' t fctx seen
recursivep' (Pair t s) fctx seen = recursivep' t fctx seen && recursivep' s fctx seen
recursivep' (Inl t _) fctx seen = recursivep' t fctx seen
recursivep' (Inr t _) fctx seen = recursivep' t fctx seen
recursivep' (Fold t _) fctx seen = recursivep' t fctx seen
recursivep' (Unfold t _) fctx seen = recursivep' t fctx seen
recursivep' (Case t _ s _ r) fctx seen = recursivep' t fctx seen && recursivep' s fctx seen && recursivep' r fctx seen
recursivep' (Split t _ _ s) fctx seen = recursivep' t fctx seen && recursivep' s fctx seen
recursivep' (Lambda x ty t) fctx seen = recursivep' t fctx seen
recursivep' (TLambda x t) fctx seen = recursivep' t fctx seen
recursivep' (Ev t s) fctx seen = recursivep' s fctx seen
