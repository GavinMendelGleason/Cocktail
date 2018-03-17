module Soundness where 

import Derivation 
import Lang 
import Eval
import Exceptions
import Data.Foldable (foldrM)
import Choice 
import Control.Monad
import Generalise
import Data.List
import Debug.Trace
import Data.Maybe
import Control.Monad.Error
import Utils
-- Paths 

data RuleTag = PointerTag Int
             | DeltaTag
             | ImpElimTag1
             | ImpElimTag2 
             | ImpIntroTag
             | AllIntroTag
             | AllElimTag
             | AndIntroTag1 
             | AndIntroTag2
             | AndElimTag1 
             | AndElimTag2
             | MuIntroTag -- Could use a single AlphaIntro but I'm not sure of the impact on totality checking
             | NuIntroTag
             | AlphaElimTag
             | OrIntroLTag 
             | OrIntroRTag 
             | OrElimTag1 
             | OrElimTag2
             | OrElimTag3 deriving Show
                
type Path = [Holds]
type Tags = [RuleTag]

-- collects all cyclic paths which for which this Holds is a recurrance.
paths :: PreProof -> [Path] 
paths d = paths' 0 d

paths' :: Int -> PreProof -> [Path]
paths' n (Pointer h m l) = if n == m then return [h] else concat $ map (paths' (n+1)) l
paths' n (DeltaRule h a) = do 
  l <- paths' (n+1) a
  return (h:l)
paths' n (VarIntro h) = mzero
paths' n (FunIntro h) = mzero
paths' n (UnitIntro h) = mzero
paths' n (ImpElim h a b) = do 
  l <- paths' (n+1) a 
  return (h:l)
 |+| do
  l <- paths' (n+1) b
  return (h:l)
paths' n (ImpIntro h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (AllIntro h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (AllElim h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (AndIntro h a b) = do 
  l <- paths' (n+1) a 
  return (h:l)
 |+| do
  l <- paths' (n+1) b
  return (h:l)
paths' n (AndElim h a b) = do 
  l <- paths' (n+1) a 
  return (h:l)
 |+| do
  l <- paths' (n+1) b
  return (h:l)
paths' n (AlphaIntro h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (AlphaElim h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (OrIntroL h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (OrIntroR h a) = do 
  l <- paths' (n+1) a 
  return (h:l)
paths' n (OrElim h a b c) = do 
  l <- paths' (n+1) a 
  return (h:l)
 |+| do
  l <- paths' (n+1) b
  return (h:l)
 |+| do
  l <- paths' (n+1) c
  return (h:l)

tags :: PreProof -> [Tags] 
tags d = tags' 0 d

tags' :: Int -> PreProof -> [Tags]
tags' n (Pointer h m l) = if n == m 
                          then return []
                          else mzero -- snd $ mapAccumL (\ acc t -> (acc+1,(PointerTag acc):t)) 0 $ concat $ map (tags' (n+1)) l
tags' n (DeltaRule h a) = do 
  l <- tags' (n+1) a
  return (DeltaTag:l)
tags' n (VarIntro h) = mzero
tags' n (FunIntro h) = mzero
tags' n (UnitIntro h) = mzero
tags' n (ImpElim h a b) = do 
  l <- tags' (n+1) a 
  return (ImpElimTag1:l)
 |+| do
  l <- tags' (n+1) b
  return (ImpElimTag2:l)
tags' n (ImpIntro h a) = do 
  l <- tags' (n+1) a 
  return (ImpIntroTag:l)
tags' n (AllIntro h a) = do 
  l <- tags' (n+1) a 
  return (AllIntroTag:l)
tags' n (AllElim h a) = do 
  l <- tags' (n+1) a 
  return (AllElimTag:l)
tags' n (AndIntro h a b) = do 
  l <- tags' (n+1) a 
  return (AndIntroTag1:l)
 |+| do
  l <- tags' (n+1) b
  return (AndIntroTag2:l)
tags' n (AndElim h a b) = do 
  l <- tags' (n+1) a 
  return (AndElimTag1:l)
 |+| do
  l <- tags' (n+1) b
  return (AndElimTag2:l)
tags' n (AlphaIntro (Holds _ _ _ _ (Nu _ _)) a) = do 
  l <- tags' (n+1) a 
  return (NuIntroTag:l)
tags' n (AlphaIntro (Holds _ _ _ _ (Mu _ _)) a) = do 
  l <- tags' (n+1) a 
  return (MuIntroTag:l)
tags' n (AlphaElim h a) = do 
  l <- tags' (n+1) a 
  return (AlphaElimTag:l)
tags' n (OrIntroL h a) = do 
  l <- tags' (n+1) a 
  return (OrIntroLTag:l)
tags' n (OrIntroR h a) = do 
  l <- tags' (n+1) a 
  return (OrIntroRTag:l)
tags' n (OrElim h a b c) = do 
  l <- tags' (n+1) a 
  return (OrElimTag1:l)
 |+| do
  l <- tags' (n+1) b
  return (OrElimTag2:l)
 |+| do
  l <- tags' (n+1) c
  return (OrElimTag3:l)

pgr :: RuleTag -> Bool
pgr NuIntroTag = True
pgr _ = False

pgreq :: RuleTag -> Bool
pgreq OrElimTag2 = True
pgreq OrElimTag3 = True
pgreq AndElimTag2 = True 
pgreq AllElimTag = True
pgreq AllIntroTag = True
pgreq DeltaTag = True
pgreq MuIntroTag = True
pgreq OrIntroLTag = True
pgreq OrIntroRTag = True
pgreq AndIntroTag1 = True
pgreq AndIntroTag2 = True
pgreq ImpIntroTag = True
pgreq tag = pgr tag

coinductive_path [] = False
coinductive_path (h1:[]) = False
coinductive_path (tag:rest) = pgr tag && admissable_path rest
                              || pgreq tag && coinductive_path rest

admissable_path [] = True
admissable_path (tag:rest) = pgreq tag && admissable_path rest

casvar (Case t x r y s) = casvar t
casvar (Unfold t ty) = casvar t
casvar (V n) = Just n
casvar _ = Nothing

splitvar (Split t x y s) = splitvar t 
splitvar (Unfold t ty) = splitvar t
splitvar (V n) = Just n
splitvar _ = Nothing

liftrel :: Int -> [(Var,Term)] -> [(Var,Term)]
liftrel n = map (\ (x,y) -> (x,shift y 0 n)) 

inductive_candidates :: Path -> [(Var,Term)] -> Holds -> [(Var,Term)]
inductive_candidates [] rel h = []
inductive_candidates (h1:[]) rel h = 
    case h >- h1 of 
      Nothing -> error ("Not possible to have no instance for derivation: "++show h ++"!>-"++show h1)
      Just rel' -> rel `intersect` rel'
inductive_candidates ((Holds _ vc _ (Case t x r y s) _):(h1@(Holds _ vc' _ u _)):rest) rel h = 
    if length vc' - length vc > 0
    then case casvar t of 
           Nothing -> inductive_candidates (h1:rest) (liftrel 1 rel) h
           Just n -> inductive_candidates (h1:rest) ((n,V 0):(liftrel 1 rel)) h
    else inductive_candidates (h1:rest) rel h
inductive_candidates ((Holds _ vc _ (Split t x y s) _):(h1@(Holds _ vc' _ u _)):rest) rel h = 
    if length vc' - length vc > 0
    then case splitvar t of 
           Nothing -> inductive_candidates (h1:rest) (liftrel 2 rel) h
           Just n -> inductive_candidates (h1:rest) ((n,V 1):(n,V 0):(liftrel 2 rel)) h
    else inductive_candidates (h1:rest) rel h
inductive_candidates ((Holds _ vc _ _ _):(h1@(Holds _ vc' _ u _)):rest) rel h = 
    let l = length vc' - length vc
    in inductive_candidates (h1:rest) (liftrel l rel) h

-- liftrel :: [(Int,Int)] -> [(Int,Int)]
-- liftrel l = map (\ (x,y) -> (x+1,y+1)) l

bigintersect [] = []
bigintersect (r:[]) = r
bigintersect (r:rest) = r `intersect` (bigintersect rest)

isTotal :: PreProof -> Bool 
isTotal = isJust . eitherToMaybe . isProof

type Inductive = Bool 
type Coinductive = Bool
type Modality = (Inductive,Coinductive)

isMu (Mu v ty) = True 
isMu _ = False

isNu (Nu v ty) = True
isNu _ = False 

--modality :: Type -> Modality
-- modality (Mu v ty) = (True,False)
-- modality (Nu v ty) = (False,True)
-- modality (All v ty) = modality ty
-- modality (Imp tya tyb) = 
--     let l = isMu tya 
--         (h,i) = modality tyb
--     in (l || h, i)
-- modality _ = (False,False)

-- Tie fighters are either disjunctions
(|<+>|) :: Either String () -> Either String () -> Either String ()
(|<+>|) (Right x) _ = Right x
(|<+>|) _ (Right x) = Right x 
(|<+>|) (Left x) (Left y) = Left ("Failure for both:\n"++x++"\n"++y)

-- Either String () is essentially a boolean type carrying an error message for failure.  return () = true, throw EXN = false
isProof :: PreProof -> Either String ()
isProof (VarIntro h) = return ()
isProof (Pointer h n l) = foldrM (\ a _ -> isProof a) () l 
isProof (FunIntro h) = throwError $ "Bare function symbols can not be type checked: "++(show h)
isProof (UnitIntro h) = return ()
isProof d = 
    let h = proofSequent d
        ty = sequentType h
        ps = paths d
    in if null ps
       then foldrM (\ a _ -> isProof a) () (antecedents d)
       else (let rs = bigintersect (map (\ p -> inductive_candidates p [] h) ps)
             in if rs == [] && length ps > 0 
                then throwError $ "The paths: "++(show ps)++" are not inductive"
                else foldrM (\ a _ -> isProof a) () (antecedents d))                
           |<+>| (if isNu ty
                  then let ts = {- trace ((show ps)++(show (tags d))) -} (tags d)
                           rs = foldr (\ p r -> coinductive_path p && r) True ts
                       in if rs
                          then foldrM (\ a _ -> isProof a) () (antecedents d)
                          else throwError $ "The tags: "++(show ts)++" are not coinductive"
                else throwError "No cycles possible with this type.")

antecedents :: PreProof -> [PreProof]
antecedents (AlphaIntro h a) = [a]
antecedents (AlphaElim h a) =  [a]
antecedents (DeltaRule h a) = [a]
antecedents (VarIntro h) = []
antecedents (Pointer h n l) = l
antecedents (FunIntro h) = []
antecedents (UnitIntro h) = []
antecedents (ImpIntro h a) = [a]
antecedents (ImpElim h a b) = [a,b]
antecedents (AllIntro h a) = [a]
antecedents (AllElim h a) = [a]
antecedents (AndIntro h a b) = [a,b]
antecedents (AndElim h a b) = [a,b]
antecedents (OrIntroL h a) = [a]
antecedents (OrIntroR h a) = [a]
antecedents (OrElim  h a b c) = [a,b,c]

typeCorrect :: FunCtx -> VarCtx -> TypeCtx -> Term -> Either String ()
typeCorrect fctx vctx tctx t = do 
  d <-makeProof fctx vctx tctx t
  isProof d

position :: [RuleTag] -> PreProof -> Maybe PreProof
position [] d = Just d
position ((PointerTag i):rest) (Pointer _ _ l) =  ith i l >>= (position rest)
position (DeltaTag:rest) (DeltaRule _ e) = position rest e
position (ImpElimTag1:rest) (ImpElim _ e _) = position rest e
position (ImpElimTag2:rest) (ImpElim _ _ e) = position rest e
position (ImpIntroTag:rest) (ImpIntro _ e) = position rest e
position (AllIntroTag:rest) (AllIntro _ e) = position rest e
position (AllElimTag:rest) (AllElim _ e) = position rest e
position (AndIntroTag1:rest) (AndIntro _ e _) = position rest e
position (AndIntroTag2:rest) (AndIntro _ _ e) = position rest e
position (AndElimTag1:rest) (AndElim _ e _) = position rest e
position (AndElimTag2:rest) (AndElim _ _ e) = position rest e
position (MuIntroTag:rest) (AlphaIntro _ e) = position rest e
position (NuIntroTag:rest) (AlphaIntro _ e) = position rest e
position (AlphaElimTag:rest) (AlphaElim _ e) = position rest e
position (OrIntroLTag:rest) (OrIntroL _ e) = position rest e
position (OrIntroRTag:rest) (OrIntroR _ e) = position rest e
position (OrElimTag1:rest) (OrElim _ e _ _) = position rest e
position (OrElimTag2:rest) (OrElim _ _ e _) = position rest e
position (OrElimTag3:rest) (OrElim _ _ _ e) = position rest e
position rt d = trace ("Died here..."++show rt ++ show d) Nothing

replace :: [RuleTag] -> PreProof -> PreProof -> Maybe PreProof
replace [] s d = return s
replace ((PointerTag i):rest) s (Pointer h j l) = do 
  e <- (ith i l) >>= replace rest s
  left <- ith i (inits l)
  right <- ith (i+1) (tails l)
  return $ Pointer h j (left++[e]++right)
replace (DeltaTag:rest) s (DeltaRule h e) = do 
  e' <- replace rest s e
  return $ DeltaRule h e'
replace (ImpElimTag1:rest) s (ImpElim h e f) = do
  e' <- replace rest s e
  return $ ImpElim h e' f
replace (ImpElimTag2:rest) s (ImpElim h e f) = do 
  f' <- replace rest s f
  return $ ImpElim h e f'
replace (ImpIntroTag:rest) s (ImpIntro h e) = do
  e' <- replace rest s e
  return $ ImpIntro h e' 
replace (AllIntroTag:rest) s (AllIntro h e) = do  
  e' <- replace rest s e
  return $ AllIntro h e'
replace (AllElimTag:rest) s (AllElim h e) = do  
  e' <- replace rest s e
  return $ AllElim h e'
replace (AndIntroTag1:rest) s (AndIntro h e f) = do 
  e' <- replace rest s e
  return $ AndIntro h e' f
replace (AndIntroTag2:rest) s (AndIntro h e f) = do 
  f' <- replace rest s f
  return $ AndIntro h e f'
replace (AndElimTag1:rest) s (AndElim h e f) = do 
  e' <- replace rest s e
  return $ AndElim h e' f
replace (AndElimTag2:rest) s (AndElim h e f) = do 
  f' <- replace rest s f
  return $ AndElim h e f'
replace (MuIntroTag:rest) s (AlphaIntro h e) = do 
  e' <- replace rest s e
  return $ AlphaIntro h e'
replace (NuIntroTag:rest) s (AlphaIntro h e) = do 
  e' <- replace rest s e
  return $ AlphaIntro h e'
replace (AlphaElimTag:rest) s (AlphaElim h e) = do 
  e' <- replace rest s e
  return $ AlphaElim h e'
replace (OrIntroLTag:rest) s (OrIntroL h e) = do
  e' <- replace rest s e
  return $ OrIntroL h e'
replace (OrIntroRTag:rest) s (OrIntroR h e) = do 
  e' <- replace rest s e
  return $ OrIntroR h e'
replace (OrElimTag1:rest) s (OrElim h e f g) = do 
  e' <- replace rest s e
  return $ OrElim h e' f g
replace (OrElimTag2:rest) s (OrElim h e f g) = do 
  f' <- replace rest s f
  return $ OrElim h e f' g
replace (OrElimTag3:rest) s (OrElim h e f g) = do 
  g' <- replace rest s g
  return $ OrElim h e f g'
replace _ _ _ = Nothing

up :: [RuleTag] -> [RuleTag]
up [] = []
up rt = init rt

down :: Int -> PreProof -> Maybe RuleTag
down 0 (DeltaRule _ _) = return DeltaTag
down 0 (ImpElim _ _ _) = return ImpElimTag1
down 1 (ImpElim _ _ _) = return ImpElimTag2
down 0 (ImpIntro _ _) = return ImpIntroTag
down 0 (AllIntro _ _) = return AllIntroTag
down 0 (AllElim _ _) = return AllElimTag
down 0 (AndIntro _ _ _) = return AndIntroTag1
down 1 (AndIntro _ _ _) = return AndIntroTag2
down 0 (AndElim _ _ _) = return AndElimTag1
down 1 (AndElim _ _ _) = return AndElimTag2
down 0 (AlphaIntro (Holds _ _ _ _ (Mu _ _)) _) = return MuIntroTag
down 0 (AlphaIntro (Holds _ _ _ _ (Nu _ _)) _) = return NuIntroTag
down 0 (AlphaElim _ _) = return AlphaElimTag
down 0 (OrIntroL _ _) = return OrIntroLTag
down 0 (OrIntroR _ _) = return OrIntroRTag
down 0 (OrElim _ _ _ _) = return OrElimTag1
down 1 (OrElim _ _ _ _) = return OrElimTag2
down 2 (OrElim _ _ _ _) = return OrElimTag3
down i (Pointer _ _ _) = return $ PointerTag i
down _ _ = Nothing

path :: [RuleTag] -> PreProof -> Maybe Path 
path [] d = return []
path (tag:rest) d = do
  let h = (proofSequent d)
  d' <- position [tag] d 
  p <- path rest d'
  return (h:p)