# Cocktail
Supercompiler for a variant of System-F(omega)

*  cocktail-src/ 
Contains programmes which can be used as definitions for the evaluator

You can get started by reading the online help as follows

```
gavin@chemnitz:~/Documents/build/Cocktail$ ./Cocktail
Cocktail> :help

:load filename		To Load a file
:quit			To quit Poitin
:out [filename]		Output program to file
:proof [filename]		Output derivation to PDF file
:super			Supercompile the current program
:reify		Reify term as program
:check		Check totality of the program
:total [n]			Supercompile the current program searching for a provably total representative over n proofs
:help			Show this message
:program		To print the current program
:down [n]		Descend further into a term taking the n'th branch
:up		Ascend once step to the containing context term
:top		Ascend to the top level closed term
:norm		Normalise the present term
:display		Show pdf of derivation
:unfold		Unfold the blocking term
:fold		Fold a term with a prior term
:term		Show the present term
Cocktail> 
```
## Syntax

The intended syntax is given by the following more common symbolic forms on the right. 

### Terms
```
\ x : (A) . r := λx : A.r
inr(r,A)      := right(r, A)
inl(r,A)      := left(r, A)
(r,s)         := (r, s)
/\ X . r      := ΛX.r
case t of { inl(x) => r | inr(y) => s } 
              := case t of {x ⇒ r | y ⇒ s}
split t as (x,y) in {r} := split t as (x, y) in r
fold(r,A) := inα(r, A)
unfold(r,A) := outα(r, A)
```
### Types
```
A * B     := A × B
A+B       := A + B
A -> B    := A → B
\-/ X . A := ∀X.A
nu X .(A) := νX.A
mu X .(A) := µX.A
```

### Files 

The general syntax of Cocktail files is: 

```
term
where
 function_constant1 : type1 = term1 
 ...
 function_constantn : typen = termn
```

For instance, the following gives the `even` function which returns true if a natural number is even, and false if not.

```
even

where 

true : 1+1 = inl(U,1+1);
false : 1+1 = inr(U,1+1);

even : (mu N . 1+N) -> (1+1) = 
     \ x : (mu N . 1+N) . 
        case unfold(x, (mu N.1+N)) of 
	 { inl(z) => inl(U,1+1)
	 | inr(x') => case even x' of 
	               { inl(t) => inr(U,1+1)
		       | inr(f) => inl(U,1+1)}};
```
