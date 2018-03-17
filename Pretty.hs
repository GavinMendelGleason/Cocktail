module Pretty where 

import Data.List
import Lang
import Utils
import Exceptions

instance Show Type where 
    show ty = show_type ty []

class (Prec a) where 
    prec :: a -> Int 

instance (Prec Type) where 
    prec One = 1
    prec (TV _) = 1
    prec (And _ _) = 2
    prec (Or _ _) = 3
    prec (Imp _ _) = 4
    prec (All _ _) = 5
    prec (Nu _ _) = 5
    prec (Mu _ _) = 5

instance (Prec Term) where 
    prec Unit = 1
    prec (V _) = 1
    prec (F _) = 1
    prec (App _ _) = 3
    prec (TApp _ _) = 3
    prec (Pair _ _) = 2
    prec (Inl _ _) = 2
    prec (Inr _ _) = 2
    prec (Fold _ _) = 2
    prec (Unfold _ _) = 2 
    prec (Case _ _ _ _ _) = 3
    prec (Split _ _ _ _) = 3
    prec (Lambda _ _ _) = 4
    prec (TLambda _ _) = 4

mwrap i j s = if prec i >= prec j
              then "("++ s ++")"
              else s

show_type One tctx = "1"
show_type (FT i) tctx = "%"++i
show_type (TV n) tctx = if length tctx > n then tctx!!n else ("#"++show n)
show_type ty@(And s t) tctx = mwrap s ty (show_type s tctx)
                              ++" * "
                              ++ mwrap t ty (show_type t tctx)
show_type ty@(Or s t) tctx = mwrap s ty (show_type s tctx)
                             ++" + "
                             ++ mwrap t ty (show_type t tctx)
show_type ty@(Imp s t) tctx = mwrap s ty (show_type s tctx)
                              ++" -> "
                              ++ mwrap t ty (show_type t tctx)
show_type ty@(All v t) tctx = let v' = freshen v tctx 
                              in "\\-/ "++v'++"."++(show_type t (v':tctx))
show_type ty@(Nu v t) tctx = let v' = freshen v tctx 
                             in "nu "++v'++"."++(show_type t (v':tctx))
show_type ty@(Mu v t) tctx = let v' = freshen v tctx
                             in "mu "++v'++"."++(show_type t (v':tctx))

instance Show Term where 
    show t = show_term t [] []

instance Show Holds where 
    show (Holds fctx vctx tctx t ty) = showTermCtx vctx tctx ++ "," ++ showTypeCtx tctx ++ " |- " ++ show_term t vctx tctx++" : "++show_type ty tctx

showTypeCtx tctx = "["++(concat $ intersperse "," tctx)++"]"

showTermCtx vctx tctx = "["++(concat $ intersperse "," $ map (\ (x,ty) -> x++":"++ groupType ty (show_type ty tctx)) vctx)++"]"

show_term :: Term -> VarCtx -> TypeCtx -> String
show_term t ctx tctx = show_term' t ctx tctx 0

show_term' (V v) ctx tctx il = if length ctx > v then fst (ctx!!v) else ("#"++show v)
show_term' (F f) ctx tctx il = f 
show_term' Unit ctx tctx il = "U"
show_term' u@(App t s) ctx tctx il = let str = mwrap t u (show_term' t ctx tctx il)
                                         sl = length str + 1
                                     in str++" "++ mwrap s u (show_term' s ctx tctx (il+sl))
show_term' u@(TApp t s) ctx tctx il = mwrap t u (show_term' t ctx tctx il) ++" ["++show_type s tctx++"]"
show_term' u@(Pair t s) ctx tctx il = let str = "(" ++ mwrap t u (show_term' t ctx tctx il)
                                          sl = length str + 1
                                      in str++","++mwrap s u (show_term' s ctx tctx (il+sl)) ++ ")"
show_term' u@(Inl t ty) ctx tctx il = "inl("++show_term' t ctx tctx (il+4) ++","++show_type ty tctx++")"
show_term' u@(Inr t ty) ctx tctx il = "inr("++show_term' t ctx tctx (il+4) ++","++show_type ty tctx++")"
show_term' u@(Fold t ty) ctx tctx il = "fold("++show_term' t ctx tctx (il+5) ++","++show_type ty tctx++")"
show_term' u@(Unfold t ty) ctx tctx il = "unfold("++show_term' t ctx tctx (il+6) ++","++show_type ty tctx++")"
show_term' (Case t x r y s) ctx tctx il = let x' = freshen x (map fst ctx)
                                              y' = freshen y (x':(map fst ctx))
                                          in "case "++show_term' t ctx tctx (il+5) ++" of \n"++ 
                                             replicate (il+3) ' ' ++ "{inl("++x'++") =>\n"++
                                             replicate (il+5) ' ' ++ show_term' r ((x',One):ctx) tctx (il+5)++"\n"++
                                             replicate (il+3) ' ' ++ "|inr("++y'++") =>\n"++
                                             replicate (il+5) ' ' ++show_term' s ((y',One):ctx) tctx (il+5)++"}"
show_term' (Split t x y s) ctx tctx il = let x' = freshen x (map fst ctx)
                                             y' = freshen y (x':(map fst ctx))
                                         in "split "++show_term' t ctx tctx (il+6)++"\n"++ 
                                            replicate il ' ' ++ "as ("++ x'++","++y'++")\n"++
                                            replicate il ' ' ++ "in {"++show_term' s ((x',One):(y',One):ctx) tctx (il+4) ++"}"
show_term' u@(Lambda x ty t) ctx tctx il = let (al,t') = lambdaListAndTerm u
                                               al' = foldr (\ (v,ty) r -> ((freshen v ((map fst r)++(map fst ctx))),ty):r) [] al
                                               str = showLambdaList (reverse al') tctx
                                           in "\\ "++str++".\n"++
                                              replicate (il+3) ' ' ++ show_term' t' (al'++ctx) tctx (il+3)
show_term' u@(TLambda x t) ctx tctx il = let (al,t') = tlambdaListAndTerm u
                                             al' = foldr (\ v r -> (freshen v (r++tctx)):r) [] al
                                             str = concat $ intersperse " " (reverse al')
                                         in "/\\" ++str++".\n"++
                                            replicate (il+3) ' ' ++ show_term' t' ctx (al'++tctx) (il+3)

lambdaListAndTerm t = lambdaListAndTerm' t [] 
    where 
      lambdaListAndTerm' (Lambda x ty t) xs = lambdaListAndTerm' t ((x,ty):xs)
      lambdaListAndTerm' t xs = (xs,t)

groupType (TV i) s = s 
groupType _ s = "("++s++")"

showLambdaList xs tctx = concat $ intersperse " " $ map (\ (x,ty) -> x++":"++ groupType ty (show_type ty tctx)) xs

tlambdaListAndTerm t = tlambdaListAndTerm' t []
    where
      tlambdaListAndTerm' (TLambda x t) xs = tlambdaListAndTerm' t (x:xs)
      tlambdaListAndTerm' t xs = (xs,t)

showHistory ls = showHistory' ls 1
    where
      showHistory' [] n = ""
      showHistory' ((Holds _ vctx tctx t _):rest) n = show n ++ ". " ++ show_term t vctx tctx ++ "\n" ++ showHistory' rest (n+1)