module Generalise where 

import Data.List (sortBy,union)
import Lang
import Eval
import Pretty
import Utils
import Exceptions
import Debug.Trace 
import Derivation
import Normalise
import Control.Monad.Error
import Data.Foldable (foldrM,foldlM)

-- >-
{- 
(>-) :: Holds -> Holds -> Maybe [(Int,Term)]
(>-) (fctx,ctx,tctx,t,ty) (fctx',ctx',tctx',t',ty') = do 
  tysub <- type_instance ty ty' (length tctx) [] 
  let (vars,types) = unzip tysub
  let tsubed = type_sub_term types vars t (length tctx)
  inst t t' ctx (length ctx) []
-}

type Sub = [(Int,Term)]
subIdx (i,_) = i

(>-) :: Holds -> Holds -> Maybe Sub
(>-) h1@(Holds fctx ctx tctx t ty) h2@(Holds fctx' ctx' tctx' t' ty') = 
    let sub = {- trace ("Starting Inst..."++show h1++","++show h2) -} (inst t t' 0 [])
    in case sub of 
         Nothing -> sub 
         Just _ -> {- trace ("\nInstance: "++show h1 ++ ", "++show h2++" "++show sub) -} sub

type TypeSub = [(Int,Type)]
(>*-) :: Holds -> Holds -> Maybe TypeSub
(>*-) h1@(Holds fctx ctx tctx t ty) h2@(Holds fctx' ctx' tctx' t' ty') = type_instance ty ty' 0 []

type_instance :: Type -> Type -> Int -> TypeSub -> Maybe TypeSub
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
type_instance (TV i) ty' d env | i >= d =
  case lookup (i-d) env of 
    Nothing -> return $ (i,ty'):env
    Just ty -> if ty == type_shift' ty' d (-d)
               then return $ env
               else Nothing
type_instance ty1 ty2 d env = Nothing

inst ::  Term -> Term -> Int -> Sub -> Maybe Sub
inst (V i) (V j) d env | i < d = 
    if i == j 
    then return env 
    else Nothing
inst (F f) (F g) d env = 
    if f == g
    then return env 
    else Nothing
inst (Inl t ty) (Inl t' ty') d env = do 
  inst t t' d env 
inst (Inr t ty) (Inr t' ty') d env = do 
  inst t t' d env 
inst (Fold t ty) (Fold t' ty') d env = do 
  inst t t' d env
inst (Pair t s) (Pair t' s') d env = do 
  env' <- inst t t' d env
  inst s s' d env'
inst (Lambda x ty t) (Lambda x' ty' t') d env = do 
  inst t t' (d+1) env
inst (TLambda x t) (TLambda x' t') d env = do
  inst t t' d env
inst (Case t x r y s) (Case t' x' r' y' s') d env = do 
  env' <- inst t t' d env
  env'' <- inst r r' (d+1) env'
  inst s s' (d+1) env''
inst (Split t x y r) (Split t' x' y' r') d env = do 
  env' <- inst t t' d env 
  inst r r' (d+2) env'
inst (Unfold t ty) (Unfold t' ty') d env = do 
  inst t t' d env 
inst (App r s) (App r' s') d env = do 
  env' <- inst r r' d env 
  inst s s' d env'
inst (TApp t ty) (TApp t' ty') d env = do 
  inst t t' d env 
inst (V i) t' d env | i >= d = 
  case lookup (i-d) env of 
    Nothing -> return $ (i-d,shift t' d (-d)):env
    Just t -> if t == shift t' d (-d)
              then return $ env
              else Nothing
inst _ _ _ _ = Nothing

-- Named "sub pair" because it's a datastructur holding two substitutions. 
type TypeSubPair = [(TVar,Type,Type)]
-- Var: Index into extendent context
-- Term1: Generalised Term 
-- Term2: Original Term 1
-- Term3: Original Term 2
-- Term4: Substitution Term 
-- Term5: Substitution Term 
-- Term6: Type of Generalised Term
type SubPair = [(Var,Term,Term,Term,Term,Term,Type)]

find_tsub :: TypeSubPair -> Type -> Type -> Maybe TVar
find_tsub [] _ _ = Nothing
find_tsub ((k,tya,tyb):tsub) ty1 ty2 = 
    if  ty1 == tya && ty2 == tyb
    then return k
    else find_tsub tsub ty1 ty2

find_sub :: SubPair -> Term -> Term -> Maybe Term
find_sub [] _ _ = Nothing
find_sub ((i,r,s,t,_,_,_):rest) t1 t2 = 
    if s == t1 && t == t2
    then return r
    else find_sub rest t1 t2

isVar (V i) = True
isVar _ = False 

generalise_type :: TypeCtx -> Int -> TypeSubPair -> Type -> Type -> (TypeCtx,TypeSubPair,Type)
generalise_type ext lb tsub (TV i) (TV j) | i == j = (ext,tsub,TV i)
generalise_type ext lb tsub One One = (ext,tsub,One)
generalise_type ext lb tsub (And tya1 tyb1) (And tya2 tyb2) = 
    let (ext',tsub',tya) = generalise_type ext lb tsub tya1 tya2 
        (ext'',tsub'',tyb) = generalise_type ext' lb tsub' tyb1 tyb2
    in (ext'',tsub'',And tya tyb)
generalise_type ext lb tsub (Or tya1 tyb1) (Or tya2 tyb2) = 
    let (ext',tsub',tya) = generalise_type ext lb tsub tya1 tya2 
        (ext'',tsub'',tyb) = generalise_type ext' lb tsub' tyb1 tyb2
    in (ext'',tsub'',Or tya tyb)
generalise_type ext lb tsub (Imp tya1 tyb1) (Imp tya2 tyb2) = 
    let (ext',tsub',tya) = generalise_type  ext lb tsub tya1 tya2 
        (ext'',tsub'',tyb) = generalise_type  ext' lb tsub' tyb1 tyb2
    in (ext'',tsub'',Imp tya tyb)
generalise_type ext lb tsub (All n ty1) (All m ty2) = 
    let (ext',tsub',ty) = generalise_type ext (lb+1) tsub ty1 ty2
    in (ext',tsub',All n ty)
generalise_type ext lb tsub (Nu n ty1) (Nu m ty2) = 
    let (ext',tsub',ty) = generalise_type ext (lb+1) tsub ty1 ty2
    in (ext',tsub',Nu n ty)
generalise_type ext lb tsub (Mu n ty1) (Mu m ty2) = 
    let (ext',tsub',ty) = generalise_type ext (lb+1) tsub ty1 ty2
    in (ext',tsub',Mu n ty)
generalise_type ext lb tsub ty1 ty2 = 
    case find_tsub tsub ty1 ty2 of 
      Just k -> (ext,tsub,TV k)
      Nothing -> let v = freshen "A" ext
                     i = length ext
                     ext' = ext ++ [v]
                     tsub' = (i,ty1,ty2):tsub
                 in (ext',tsub',TV (i+lb))

generalise :: MonadError String m => Holds -> Holds -> m (TypeCtx,VarCtx,TypeSubPair,SubPair,Term,Type)
generalise (Holds fctx vctx tctx t ty) (Holds fctx' vctx' tctx' t' ty') = 
    if fctx /= fctx' then throwError "Incompatible function contexts" -- sanity check 
    else let (tcext, tsub, at_type) = generalise_type [] 0 [] ty ty' 
         in do 
           (vcext2,tcext2,sub2,tsub2,g) <- generalise' fctx vctx vctx' tctx tctx' [] tcext 0 0 [] tsub t t' at_type
           return (tcext2,vcext2,tsub2,sub2,g,at_type)
           {-
           -- check to see if the generalisation is trivial
           if not (all (\ (_,_,_,x,_) -> isVar x) sub2)
             then return (tcext2,vcext2,tsub2,sub2,g,at_type)
             else throwError "Useless generalisation - simply a renaming." -}

{- 
Generalisation 
fctx := Function context for both 
vctx := Var context for the first term 
vctx' := Var context for the second term
tctx := Type context for the first term 
tctx' := Type context for the second term
vcext := extended context that will occur at the top level - outside all current binders, 
         but below the generalisation context (free variables) of either.
lb := number of lambda binders up to the context of generalisation
sub := the substitution that we have constructed so far
Term := first term to generalise 
Term := second term to generalise 
Type := the generalised type, at which both should be the same.  If this type is different 
        than the term structure, it is because we must generalise to a variable.
 -}
generalise' :: MonadError String m => FunCtx -> VarCtx -> VarCtx -> TypeCtx -> TypeCtx -> 
               VarCtx -> TypeCtx -> Int -> Int -> SubPair -> TypeSubPair -> 
               Term -> Term -> Type ->
               m (VarCtx,TypeCtx,SubPair,TypeSubPair,Term)
-- lb = number of lambda binders
-- tlb = number of type lambda binders
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (V i) (V j) a | i == j && i < lb = do 
  return (vcext,tcext,sub,tsub,V i)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (F f) (F g) a | f == g = do 
  return (vcext,tcext,sub,tsub,F f)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub Unit Unit One = do 
  return (vcext,tcext,sub,tsub,Unit)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (App f g) (App f' g') c = do 
  tty <- typeof fctx vctx tctx f
  tty' <- typeof fctx vctx' tctx' f'
  let (tcext1,tsub1,tgty) = generalise_type tcext tlb tsub tty tty'
  (a,b) <- case tgty of 
             Imp a b -> return (a,b)
             _ -> throwError ("Unable to generalise to an implication in "
                              ++show (Holds fctx vctx tctx f One)++","++show (Holds fctx vctx tctx f One))
  (vcext2,tcext2,sub2,tsub2,gf) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext1 lb tlb sub tsub1 f f' (Imp a b)
  (vcext3,tcext3,sub3,tsub3,gg) <- generalise' fctx vctx vctx' tctx tctx' vcext2 tcext2 lb tlb sub2 tsub2 g g' a
  return (vcext3,tcext3,sub3,tsub3,App gf gg)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Lambda x ty t) (Lambda x' ty' t') (Imp a b) = do
  (vcext1,tcext1,sub1,tsub1,g) <- generalise' fctx ((x,a):vctx) ((x',a):vctx') tctx tctx' vcext tcext (lb+1) tlb sub tsub t t' b
  return (vcext1,tcext1,sub1,tsub1,Lambda (x++"_"++x') a g)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (TLambda x t) (TLambda x' t') (All _ a) = do
  (vcext1,tcext1,sub1,tsub1,g) <- generalise' fctx vctx vctx' (x:tctx) (x':tctx') vcext tcext lb (tlb+1) sub tsub t t' a
  return (vcext1,tcext1,sub1,tsub1,TLambda (x++"_"++x') g)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Pair t s) (Pair t' s') (And a b) = do
  (vcext1,tcext1,sub1,tsub1,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub t t' a
  (vcext2,tcext2,sub2,tsub2,gb) <- generalise' fctx vctx vctx' tctx tctx' vcext1 tcext1 lb tlb sub1 tsub1 s s' b
  return (vcext2,tcext2,sub2,tsub2,Pair ga gb)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Inl t ty) (Inl t' ty') (Or a b) = do 
  (vcext1,tcext1,sub1,tsub1,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub t t' a
  return (vcext1,tcext1,sub1,tsub1,Inl ga (Or a b))
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Inr t ty) (Inr t' ty') (Or a b) = do 
  (vcext1,tcext1,sub1,tsub1,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub t t' b
  return (vcext1,tcext1,sub1,tsub1,Inr ga (Or a b))
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Unfold t (Mu x ty)) (Unfold t' (Mu x' ty')) a = do 
  let (tcext1,tsub1,gty) = generalise_type tcext (1+tlb) tsub ty ty'
  (vcext2,tcext2,sub2,tsub2,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext1 lb tlb sub tsub1 t t' (Mu x gty)
  return (vcext2,tcext2,sub2,tsub2,Unfold ga (Mu x gty))
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Unfold t (Nu x ty)) (Unfold t' (Nu x' ty')) a = do 
  let (tcext1,tsub1,gty) = generalise_type tcext (1+tlb) tsub ty ty' 
  (vcext2,tcext2,sub2,tsub2,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext1 lb tlb sub tsub1 t t' (Nu x gty)
  return (vcext2,tcext2,sub2,tsub2,Unfold ga (Nu x gty))
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Fold t ty) (Fold t' ty') (Mu x a) = do 
  (vcext1,tcext1,sub1,tsub1,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub t t' (type_sub (Mu x a) a)
  return (vcext1,tcext1,sub1,tsub1,Fold ga (Mu x a))
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Fold t ty) (Fold t' ty') (Nu x a) = do 
  (vcext1,tcext1,sub1,tsub1,ga) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub t t' (type_sub (Nu x a) a)
  return (vcext1,tcext1,sub1,tsub1,Fold ga (Nu x a))
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Case t x r y s) (Case t' x' r' y' s') c = do 
  tty <- typeof fctx vctx tctx t 
  tty' <- typeof fctx vctx' tctx' t'
  let (tcext1,tsub1,tgty) = generalise_type tcext tlb tsub tty tty'
  (a,b) <- case tgty of 
             Or a b -> return (a,b)
             _ -> throwError ("Unable to generalise to a disjunctive type in "
                              ++show (Holds fctx vctx tctx t One)++","++show (Holds fctx vctx tctx t One))
  (vcext2,tcext2,sub2,tsub2,gt) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext1 lb tlb sub tsub1 t t' tgty
  (vcext3,tcext3,sub3,tsub3,gr) <- generalise' fctx ((x,a):vctx) ((x',a):vctx') tctx tctx' vcext2 tcext2 (lb+1) tlb sub2 tsub2 r r' c
  (vcext4,tcext4,sub4,tsub4,gs) <- generalise' fctx ((y,b):vctx) ((y',b):vctx') tctx tctx' vcext3 tcext3 (lb+1) tlb sub3 tsub3 s s' c
  return (vcext4,tcext4,sub4,tsub4,Case gt x gr y gs)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub (Split t x y r) (Split t' x' y' r') c = do 
  tty <- typeof fctx vctx tctx t 
  tty' <- typeof fctx vctx' tctx' t'
  let (tcext1,tsub1,tgty) = generalise_type tcext tlb tsub tty tty'
  (a,b) <- case tgty of 
             And a b -> return (a,b)
             _ -> throwError ("Unable to generalise to a conjunctive type in "
                              ++show (Holds fctx vctx tctx t One)++","++show (Holds fctx vctx tctx t One))
  (vcext2,tcext2,sub2,tsub2,gt) <- generalise' fctx vctx vctx' tctx tctx' vcext tcext1 lb tlb sub tsub1 t t' tgty
  (vcext3,tcext3,sub3,tsub3,gr) <- generalise' fctx ((x,a):(y,b):vctx) ((x',a):(y',b):vctx') tctx tctx' 
                                   vcext2 tcext2 (lb+2) tlb sub2 tsub2 r r' c
  return (vcext3,tcext3,sub3,tsub3,Split gt x y gr)
generalise' fctx vctx vctx' tctx tctx' vcext tcext lb tlb sub tsub s t a = do
  (r,vcext',sub') <- case find_sub sub s t of 
                       Just r -> return (r,vcext,sub)
                       Nothing -> do 
                         let k = length vcext
                         let v = "v"++show k
                         -- jump outside of lambda binders => k+lb
                         (app,lams,lamt,ty) <- createPatterns (V (k+lb)) lb tlb (vctx++vcext) (tctx++tcext) tsub s t a
                         return (app,vcext++[(v,ty)],(k,app,s,t,lams,lamt,ty):sub)
  return (vcext',tcext,sub',tsub,r) 

createPatterns :: (MonadError String m) => 
                  Term -> Int -> Int -> VarCtx -> TypeCtx -> TypeSubPair -> Term -> Term -> Type -> m (Term,Term,Term,Type)
createPatterns f lb tlb vctx tctx tsub t s a = do
    let (tybvt,bvt) = boundvars lb tlb vctx t
        (tybvs,bvs) = boundvars lb tlb vctx s
        vars = bvt `union` bvs
        tyvars = tybvt `union` tybvs
        app_ = foldr (\ x r -> TApp r (TV x)) (foldr (\ x r -> App r (V x)) f vars) tyvars
        app = {- trace ("Current app: "++show app_++" vars: "++show vars++", tyvars: "++show tyvars) -} app_ 
    let t' = {- trace ("Strengthen t: "++show t) -} strengthenTerm vars tyvars t
    let s' = {- trace ("Strengthen t: "++show t) -} strengthenTerm vars tyvars s
    lamt <- foldlM (\ r i -> do
                      (v,ty) <- maybeToError (ith i vctx) $ "Corrupted context: #"++ show i ++ " " ++ show (Holds [] vctx tctx t a)
                      return $ Lambda v ty r) t' vars
    lamt' <- foldlM (\ r i -> do 
                       v <- maybeToError (ith i tctx) $ "Corrupted type context: #"++ show i ++ " " ++ show (Holds [] vctx tctx t a)
                       return $ TLambda v r) lamt tyvars
    lams <- foldlM (\ r i -> do
                      (v,ty) <- maybeToError (ith i vctx) $ "Corrupted context: #"++ show i ++ " " ++ show (Holds [] vctx tctx s a)
                      return $ Lambda v ty r) s' vars
    lams' <- foldlM (\ r i -> do 
                       v <- maybeToError (ith i tctx) $ "Corrupted type context: #"++ show i ++ " " ++ show (Holds [] vctx tctx s a)
                       return $ TLambda v r) lams tyvars
    ty <- foldlM (\ r i -> do 
                    (_,ty) <- maybeToError (ith i vctx) $ "Corrupted type context: #"++ show i ++ " " ++ show (Holds [] vctx tctx t a)
                    return $ Imp ty r) a vars
    ty' <- foldlM (\ r i -> do 
                     v <- maybeToError (ith i tctx) $ "Corrupted type context: #"++ show i ++ " " ++ show (Holds [] vctx tctx t a)
                     return $ All v r) ty tyvars
    let lamt'' = shift lamt' lb (-lb)
    let lams'' = shift lams' lb (-lb)
    return (app,lamt'',lams'',ty)


{-
genapp :: [Term] -> [Type] -> Term -> Term
genapp ts tys g = 
    let a = foldl (\ r t -> App r t) g ts
        ta = foldl (\ r ty -> TApp r ty) g tys
    in ta
-} 

genlam:: VarCtx -> TypeCtx -> Term -> Term
genlam vc tc g = 
    let l = foldl (\ r (v,t) -> Lambda v t r) g vc
        tl = foldl (\ r v -> TLambda v r) l tc
    in tl

generalised_function :: (Functor m, MonadError String m) => Holds -> Holds -> m (Holds,[Type],[Holds])
generalised_function h1 h2 = do 
  h1s@(Holds fctx vctx tctx _ _) <- maybeToError (strengthen h1) $ "Corrupted Context: "++show h1
  h2s <- maybeToError (strengthen h2) $ "Corrupted Context: "++show h2
  (tcext,vcext,tsub,sub,g,ty) <- {- trace ("\nGeneralising...\n"++show h1++"\n"++show h2) -} generalise h1s h2s
  let gl_ = {- trace ("vcext: "++show vcext) -} genlam vcext tcext g
      gl = {- trace ("Genlam: "++show (Holds fctx vctx tctx gl_ ty)) -} gl_
      ordered_sub = sortBy (\ (i,_,_,_,_,_,_) (j,_,_,_,_,_,_) -> i `compare` j) sub
      ordered_tsub = sortBy (\ (i,_,_) (j,_,_) -> i `compare` j) tsub
  let tys = map (\ (_,ty,_) -> ty) ordered_tsub
  ts <- mapM (\ (_,_,_,_,t,_,_) -> do 
                ty <- typeof fctx vctx tctx t
                return (Holds fctx vctx tctx t ty)) ordered_sub
  h <- fmap proofSequent $ makeProof fctx vctx tctx $ {- trace ("Gapp: "++show (Holds fctx vctx tctx gapp' (FT "unknown"))) -} gl
  return $ {- trace ("\nGeneralised:\n"++show h) -} (h,tys,ts)


generalisedApplication :: (Functor m, MonadError String m) => Holds -> Holds -> m PreProof
generalisedApplication h h' = do
  ((Holds fctx vctx tctx f _),typargs,termargs) <- generalised_function h h'
  let tyapp = foldr (\ ty f -> TApp f ty) f typargs
  let t = foldr (\ ha f -> App f (sequentTerm ha)) tyapp termargs
  makeProof fctx vctx tctx t
