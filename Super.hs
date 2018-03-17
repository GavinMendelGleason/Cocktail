module Super where 

import Prelude hiding (sequence)
import Control.Monad hiding (sequence)
import Lang
import Eval
import Pretty 
import Utils 
import Derivation 
import Data.List 
-- import Choice 
import Frame
import Exceptions 
-- import Monad
import Debug.Trace 
import Generalise 
import Soundness
import Data.Foldable (foldrM,foldlM) 
import Data.Maybe 
import Control.Monad.Omega
import Data.Traversable
import Normalise 
-- import Control.Monad.Error hiding (sequence)

--whistle :: Term -> Path -> Bool
--whistle t p = find

{-
focus (V i) = V i
focus (F f) = F f
focus (App f g) = focus f
focus (Case 
-}

max_depth = 100

whistle h p = 
    if length p > max_depth
    then True
    else False

couple :: Holds -> Holds -> Bool 
couple (Holds _ _ _ t _) (Holds _ _ _ t' _) = couple' t t'
    where
      couple' (Case t x s y r) (Case t' x' s' y' r') = True
      couple' (Split t x y r) (Split t' x' y' r') = True
      couple' (Inl t tyor) (Inl t' tyor') = True
      couple' (Inr t tyor) (Inr t' tyor') = True
      couple' (Pair t s) (Pair t' s') = True
      couple' (Fold t fty) (Fold t' fty') = True
      couple' _ _ = False

couples :: Holds -> Path -> Maybe (Path,Holds)
couples h p = couples' h p []
    where
      couples' :: Holds -> Path -> Path -> Maybe (Path,Holds)
      couples' h [] aux = Nothing
      couples' h (h':p) aux = if couple h h'
                              then Just (reverse aux,h')
                              else couples' h p (h':aux)

funfold :: Term -> FunCtx -> Maybe Term
funfold t fctx = 
    case split t of 
      (F f,fr) -> do 
                   fterm <- ftermlookup f fctx 
                   return $ inject fterm fr
      _ -> Nothing

unfold :: Holds -> Maybe Holds
unfold h = do 
   h'@(Holds fctx vctx tctx t ty) <- either (const Nothing) return $ propogateSequent h
   t' <- {- trace ("Unfolding: "++show h) -} funfold t fctx
   let h'' = sequentNorm $ (Holds fctx vctx tctx t' ty)
   h''' <- either (const Nothing) return $ propogateSequent h''
   return $ {- trace ("\nAs: "++show h') -} h'''

pickFrom [] = each [[]]
pickFrom (x:l) = do 
  a <- each x
  fmap (map (a:)) (pickFrom l)

placeholder = Holds [] [] [] Unit (FT "PLACEHOLDER")

super :: Path -> Holds -> Omega PreProof
super p h = 
    let h' = sequentNorm h
    in if whistle h' p
       then mzero
       else do 
         -- * Instances *
         -- find all potential instances in the history and try them each, in turn.
         (i,ts) <- each . concat $ map (\ (i,h'') -> maybeToList $ fmap (\ s -> (i, nub $ map snd s)) (h'' >- h')) (zip [0..] p)
         -- Make all possible supercompiled derivations of subterms not in the parent 
         ds <- sequence $ map (\ t -> do 
                                 let (Holds fctx vctx tctx _ _) =  h' 
                                 ty <- each . eitherToList $ typeof fctx vctx tctx t
                                 let h'' = (Holds fctx vctx tctx t ty)
                                 super (h':p) h'') ts
         return $ Pointer h' (i+1) ds 
       `mplus` do
         -- * Coupling / Generalisation *
         (_,h'') <- each . maybeToList $ couples h' p
         let oldpath = p
         (gf@(Holds fctx vctx tctx _ _),typargs,termargs) <- -- trace ("Generalising") 
                                                             each . eitherToList $ generalised_function h' h''
         let stubpath = replicate (length typargs + length termargs) placeholder -- Make sure pointers are 
                                                                                -- offset properly for upcoming applications.
         gd <- {-trace ("yes... I'm here") $-}  super (stubpath++oldpath) $ {-trace ("Generaled fun for super: "++show gf) -} gf
         let f = {- trace ("Generalised: "++ (show $ proofTerm gd)) -} proofTerm gd
             tyapp = foldr (\ ty f -> TApp f ty) f typargs
             typath = replicate (length typargs) placeholder
         (t,_) <- foldrM (\ ha (f,p) -> do 
                            d <- super p ha
                            --let a = sequentTerm ha -- 
                            let a = proofTerm d
                                t = App f a
                            return (t,placeholder:p)) (tyapp,typath++oldpath) (each termargs)
         d' <- each . eitherToList $ {- trace ("type checking..."++show (Holds fctx vctx tctx t (FT "unknown"))) -} makeProof fctx vctx tctx t
         return $ {- trace ("Final Term: "++ show (proofSequent d')) -} d'
       `mplus` do
         -- * Function constant unfolding *
         h'' <- each . maybeToList $ unfold h' -- unfold
         r <- super (h':p) h''
         return $ DeltaRule h' r
       `mplus`
         -- * Subterm supercompilation *
         super' p h' 


super' :: Path -> Holds -> Omega PreProof
super' p (Holds fctx ctx tctx (V v) ty) = each . eitherToList $ makeProof fctx ctx tctx (V v)
super' p h@(Holds fctx ctx tctx (F f) ty) = 
    case unfold h of 
      Just h' -> do 
        r <- super (h:p) h'
        return $ DeltaRule h r
      Nothing -> mzero
super' p (Holds fctx ctx tctx Unit ty) = each . eitherToList $ makeProof fctx ctx tctx Unit
super' p h@(Holds fctx ctx tctx (Pair t s) (And a b)) = do 
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t a)
  e <- super p' (Holds fctx ctx tctx s b)
  return $ AndIntro h d e
super' p h@(Holds fctx ctx tctx (Inl t ty) (Or a b)) = do 
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t a)
  return $ OrIntroL (Holds fctx ctx tctx (Inl t ty) (Or a b)) d
super' p h@(Holds fctx ctx tctx (Inr t ty) (Or a b)) = do 
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t b)
  return $ OrIntroR (Holds fctx ctx tctx (Inr t ty) (Or a b)) d
super' p h@(Holds fctx ctx tctx (Fold t (Mu x ty)) newty) = do 
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t (type_sub (Mu x ty) ty))
  return $ AlphaIntro (Holds fctx ctx tctx (Fold t (Mu x ty)) newty) d 
super' p h@(Holds fctx ctx tctx (Fold t (Nu x ty)) newty) = do 
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t (type_sub (Nu x ty) ty))
  return $ AlphaIntro (Holds fctx ctx tctx (Fold t (Nu x ty)) newty) d 
super' p h@(Holds fctx ctx tctx (TLambda x t) (All x' ty)) = do 
  let p' = h:p
  d <- super p' (Holds fctx ctx (x:tctx) t ty)
  return $ AllIntro (Holds fctx ctx tctx (TLambda x t) (All x' ty)) d
super' p h@(Holds fctx ctx tctx (Lambda x ty t) (Imp tya tyb)) = do 
  let p' = h:p
  d <- super p' (Holds fctx ((x,ty):ctx) tctx t tyb)
  return $ ImpIntro (Holds fctx ctx tctx (Lambda x ty t) (Imp tya tyb)) d
super' p h@(Holds fctx ctx tctx (Split t x y s) ty) = do
  let p' = h:p
  (And a b) <- each . eitherToList $ typeof fctx ctx tctx t 
  d <- super p' (Holds fctx ctx tctx t (And a b))
  e <- super p' (Holds fctx ((x,a):(y,b):ctx) tctx s ty)
  return $ AndElim (Holds fctx ctx tctx (Split t x y s) ty) d e
super' p h@(Holds fctx ctx tctx (Case t x r y s) ty) = do 
  let p' = h:p
  (Or a b) <- each . eitherToList $ typeof fctx ctx tctx t
  d <- super p' (Holds fctx ctx tctx t (Or a b))
  e <- super p' (Holds fctx ((x,a):ctx) tctx r ty)
  f <- super p' (Holds fctx ((y,b):ctx) tctx s ty)
  return $ OrElim (Holds fctx ctx tctx (Case t x r y s) ty) d e f
super' p h@(Holds fctx ctx tctx (App r s) ty) = do 
  let p' = h:p
  (Imp a b) <- each . eitherToList $ typeof fctx ctx tctx r
  d <- super p' (Holds fctx ctx tctx r (Imp a b))
  e <- super p' (Holds fctx ctx tctx s a)
  return $ ImpElim (Holds fctx ctx tctx (App r s) ty) d e
super' p h@(Holds fctx ctx tctx (Unfold t (Mu x ty)) ty') = do
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t (Mu x ty))
  return $ AlphaElim (Holds fctx ctx tctx (Unfold t (Mu x ty)) ty') d
super' p h@(Holds fctx ctx tctx (Unfold t (Nu x ty)) ty') = do
  let p' = h:p
  d <- super p' (Holds fctx ctx tctx t (Nu x ty))
  return $ AlphaElim (Holds fctx ctx tctx (Unfold t (Nu x ty)) ty') d
super' p h@(Holds fctx ctx tctx (TApp t ty) ty') = do 
  let p' = h:p
  a <- each . eitherToList $ typeof fctx ctx tctx t
  d <- super p' (Holds fctx ctx tctx t a)
  return $ AllElim (Holds fctx ctx tctx (TApp t ty) ty') d