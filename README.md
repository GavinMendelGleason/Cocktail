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
