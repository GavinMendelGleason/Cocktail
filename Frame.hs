module Frame where 

import Lang

data Frame = FEmpty
           | FApp Frame Term
           | FTApp Frame Type 
           | FUnfold Frame Type
           | FCase Frame Name Term Name Term
           | FSplit Frame Name Name Term

split :: Term -> (Term,Frame)
split t = split' FEmpty t 
    where split' f (App t s) = split' (FApp f s) t
          split' f (TApp t ty) = split' (FTApp f ty) t 
          split' f (Unfold t ty) = split' (FUnfold f ty) t
          split' f (Case t x r y s) = split' (FCase f x r y s) t
          split' f (Split t x y s) = split' (FSplit f x y s) t
          split' f t = (t,f)

inject t FEmpty = t
inject t (FApp f s) = inject (App t s) f
inject t (FTApp f ty) = inject (TApp t ty) f 
inject t (FUnfold f ty) = inject (Unfold t ty) f 
inject t (FCase f x r y s) = inject (Case t x r y s) f 
inject t (FSplit f x y s) = inject (Split t x y s) f

irred :: Term -> Bool 
irred t = case split t of 
            (F f,fr) -> True
            (V v,fr) -> True
            _ -> False

fblocked :: Term -> Maybe (Term,Frame)
fblocked t = case split t of 
               (F f,fr) -> Just (F f,fr)
               _ -> Nothing