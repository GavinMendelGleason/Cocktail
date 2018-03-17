module Test where 

import Lang
import Eval
import Pretty
import Derivation
import Generalise

zero = Fold (Inl Unit (Or One nat)) nat
nat = Mu "Nat" (Or One (TV 0))
suc x = Fold (Inr x (Or One nat)) nat
plusterm = Lambda "n" nat (Lambda "m" nat (Case (Unfold (V 1) nat) "z" (V 1) "n'" (suc (App (App (F "plus") (V 0)) (V 1)))))
plustype = Imp nat (Imp nat nat)
fctx = [("plus",plusterm,plustype)]
bool = Or One One
true = Inl Unit bool
false = Inr Unit bool 
term1 = (Lambda "t" bool (Case (Case (Unfold (V 0) (Or One nat)) "x" (V 0) "y" (V 0)) "u" (V 1) "w" (V 1)))
term2 = (Split (Pair true false) "x" "y" (V 0))
term3 = (Split (Split (Pair true false) "x" "y" (V 0)) "u" "v" (V 1))
-- latexprint_term t [] []
stream = (Nu "Stream" (And nat (TV 0)))
snoc x xs = (Fold (Pair x xs) stream)

term4 = (Lambda "s" stream
         (Lambda "n'" nat 
          (Lambda "m'" nat 
           (Case (App (App (F "le") (V 1)) (V 0)) 
            "t" (snoc (suc (V 2)) (App (F "g") (snoc (suc (V 1)) (V 3))))
            "f" (App (F "g") (snoc (App (F "pred") (suc (V 2))) (snoc (suc (V 1)) (V 3))))))))

holds4 = Holds fctx [] [] term4 (Imp stream (Imp nat (Imp nat stream)))
holdsfree = Holds fctx [("m", nat),("n",nat),("s",stream)] []
            (Case (App (App (F "le") (V 1)) (V 0)) 
            "t" (snoc (suc (V 2)) (App (F "g") (snoc (suc (V 1)) (V 3))))
            "f" (App (F "g") (snoc (App (F "pred") (suc (V 2))) (snoc (suc (V 1)) (V 3))))) (Imp stream (Imp nat (Imp nat stream)))