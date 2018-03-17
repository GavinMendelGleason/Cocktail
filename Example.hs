module Example where 

import Lang
import Derivation
import Eval
import Super 
import Exceptions
import Generalise 
import Frame 
import System 
import Latex 
import Soundness 
import Parse 
import Reify 
import Normalise
import Control.Monad.Omega

-- Do sumlen example
-- sumlen 
nat = (Mu "X" (Or One (TV 0)))
zero = (Fold (Inl Unit (Or One nat)) nat)
suc x = (Fold (Inr x (Or One nat)) nat)

conat = (Nu "N" (Or One (TV 0)))
cozero = (Fold (Inl Unit (Or One conat)) conat)

cosuc x = (App (F "cosuc") x)
cosucf = (Lambda "x" conat (Fold (Inr (V 0) (Or One conat)) conat))

bool = (Or One One)
stream x = (Nu "S" (And x (TV 0)))

coplus x y = (App (App (F "coplus") x) y)
coplusf = (Lambda "x" conat 
         (Lambda "y" conat 
          (Case (Unfold (V 1) conat) 
           "u" (V 1)
           "x'" (cosuc (coplus (V 0) (V 1))))))

plus x y = (App (App (F "plus") x) y)
plusf = (Lambda "x" nat 
         (Lambda "y" nat 
          (Case (Unfold (V 1) nat) 
           "u" (V 1)
           "x'" (suc (plus (V 0) (V 1))))))

sumlen x = (App (F "sumlen") x)
sumlenf = (Lambda "xs" (stream conat) 
           (Split (Unfold (V 0) (stream conat))
            "x" "xs'"
            (cosuc (coplus (V 0) (sumlen (V 1))))))

snoc x xs = (App (App (F "snoc") x) xs)
snocf = (Lambda "x" nat 
         (Lambda "xs" (stream nat) 
          (Fold (Pair (V 1) (V 0)) (stream nat))))

le n m = (App (App (F "le") n) m)
lef = parseterm_err "\\ n : (mu N.1+N) m : (mu N.1+N) .case unfold(n,(mu N.1+N)) of {inl(z) => true |inr(n') => case unfold (m,(mu N.1+N)) of {inl(z) => false | inr(m') => le n' m'}}"

pr n = (App (F "pred") n)
predf = parseterm_err "\\ n : (mu N.1+N) . case unfold(n,(mu N.1+N)) of {inl(z) => n |inr(n') => n'}"

g s = (App (F "g") s)
gf = parseterm_err "\\ s : (nu S. (mu N.1 + N) * S) . split unfold(s,(nu S. (mu N.1 + N) * S)) as (n,s') in { split unfold(s',(nu S. (mu N.1 + N) * S)) as (m,s'') in { case le n m of {inl(t) => snoc n (g (snoc m s'')) |inr(f) => g (snoc (pred n) (snoc m s'')) }}}"

botf = (F "bot")

falsety = (All "x" (TV 0))

fctx = [("cosuc",cosucf, Imp conat conat),("sumlen",sumlenf,Imp (stream conat) conat),("coplus",coplusf,Imp conat (Imp conat conat)),("plus",plusf,Imp nat (Imp nat nat)),("bot",botf,falsety),("snoc",snocf, Imp nat (Imp (stream nat) (stream nat))),("le",lef, Imp nat (Imp nat bool)), ("g",gf,(Imp (stream nat) (stream nat))), ("pred",predf,(Imp nat nat))]

super_harness t n = do 
  ty <- eitherToList $ typeof fctx [] [] t
  take n $ runOmega $ super [] (Holds fctx [] [] t ty)

hcase1 = sequent fctx [("y",nat),("x",nat)] [] (Case (Unfold (V 1) nat) "_" (V 1) "x'" (Fold (Inr (App (App (F "plus") (V 0)) (V 1)) (Or One nat)) nat))
hcase2 = sequent fctx [("x'",nat),("y",nat),("x",nat)] [] (Case (Unfold (V 0) nat) "_" (V 2) "x'" (Fold (Inr (App (App (F "plus") (V 0)) (V 2)) (Or One nat)) nat))

hlampair = sequent fctx [] [] (Lambda "y" One (Lambda "x" One (Pair (V 0) (V 0))))
hlamunit = sequent fctx [] [] (Lambda "y" One (Lambda "x" One (Pair (V 0) (V 1))))

hlamone = sequent fctx [] [] (Lambda "x" One (Lambda "y" One (V 0)))
hlamtwo = sequent fctx [] [] (Lambda "x" One (Lambda "y" One (Pair (V 0) (V 1))))

sequent :: FunCtx -> VarCtx -> TypeCtx -> Term -> Holds 
sequent fctx vctx tctx t = fromEither $ fmap proofSequent $ makeProof fctx vctx tctx t

showlatex d = do 
  writeFile "/tmp/foo.tex" (latexprint d)
  system "pdflatex --output-directory=/tmp /tmp/foo.tex"
  system "evince /tmp/foo.pdf"


foldone = sequent fctx [("m",nat),("s''",stream nat)] [] 
          (Fold (Pair (V 0) (V 1) ) (stream nat))

foldtwo = sequent fctx [("m",nat),("s''",stream nat)] [] 
          (Fold (Pair (V 0) (App (App (F "snoc") (V 0)) (V 1))) (stream nat))

generalise_harness t1 t2 = let h1 = sequent fctx [] [] t1
                               h2 = sequent fctx [] [] t2 
                           in fromEither $ generalised_function h1 h2


hc1 = sequent fctx [("s''",stream nat),("n",nat),("m",nat)] []
      (Case (le (V 1) (V 2))
       "t" (snoc (V 2) (g (snoc (V 3) (V 1))))
       "f" (g (snoc (pr (V 2)) (snoc (V 3) (V 1)))))

hc2 = sequent fctx [("s''",stream nat),("n",nat),("m",nat),("n'",nat), ("m'",nat)] []
       (Case (le (V 3) (V 4))
        "t" (snoc (V 2) (g (snoc (V 3) (V 1))))
        "f" (g (snoc (pr (V 2)) (snoc (V 3) (V 1)))))


hle = sequent fctx [("n",nat),("m",nat)] []
      (le (pr (V 0)) (V 1))

hlecase = sequent fctx [("n",nat),("m",nat)] []
          (Case (le (pr (V 0)) (V 1)) "t" (le (pr (V 1)) (V 2)) "f" (le (pr (V 1)) (V 2)))

{-
correct = "case le v0 v2 of 
            { inl(t) => snoc n (g (snoc m s''))
            | inr(f) => g (snoc (pred n) (snoc m s''))"

-}