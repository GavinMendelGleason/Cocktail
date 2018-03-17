module Latex where 

import Data.List
import Lang
import Utils
import Exceptions
import Pretty
import Derivation
import Eval (freevars)
import Data.Maybe (catMaybes)

class LatexPrint a where 
    latexprint :: a -> String

instance LatexPrint Holds where 
    latexprint (Holds fc vc tc t ty) =
        let (tvs,vs) = freevars vc t
            vc' = catMaybes $ map (\ i -> ith i vc) vs 
            tc' = catMaybes $ map (\ i -> ith i tc) tvs
        in 
        latexprint_tc tc'++","++latexprint_vc vc' tc++" \\vdash "++ 
        latexprint_term t tc vc ++ ":" ++ latexprint_type ty tc

latexprint_tc :: [Name] -> String
latexprint_tc [] = "\\cdot"
latexprint_tc (h:t) = "[" ++ latexprint_tc' (h:t)
latexprint_tc' (h:[]) = h ++ "]"
latexprint_tc' (h:t) = h ++ "," ++ latexprint_tc' t

latexprint_vc [] tc = "\\cdot"
latexprint_vc (h:t) tc = "[" ++ latexprint_vc' (h:t) tc
latexprint_vc' ((v,ty):[]) tc = v ++ ":" ++ latexprint_type ty tc ++ "]"
latexprint_vc' ((v,ty):t) tc = v ++ ":" ++ latexprint_type ty tc ++ "," ++ latexprint_vc' t tc

type_base One = True 
type_base (TV tv) = True
type_base ty = False

latex_prologue = 
    unlines
    ["\\documentclass{article}",
     "\\usepackage[active,pdftex,tightpage]{preview}",
     "\\usepackage{amsmath}",
     "\\usepackage{amssymb}",
     "\\usepackage{bussproofs}\n",
--     "\\pdfpagewidth 30in \n",
--     "\\pdfpageheight 11in \n",
--     "\\pagestyle{empty}\n",
--     "\\enlargethispage{100cm}\n\n",
--     "\\newcommand{\\cas}[5]{\\text{case}\\;{ #1 }\\;\\text{of}\\;\\text{inl}( #2 ) \\Rightarrow { #3 }\\;| \\;\\text{inr}( #4 ) \\Rightarrow { #5 }}",
--     "\\newcommand{\\spit}[4]{\\text{split}\\;{ #1 }\\;\\text{as}\\;{({#2},{#3})}\\;\\text{in}\\;{ #4 }}",
     "\\newcommand{\\spit}[4]{", 
     "  \\begin{array}[t]{l}", 
     "    \\text{split}\\;{ #1 }\\;\\text{as}\\;{({#2},{#3})}\\;\\\\", 
     "    \\text{in}\\;{ #4 }",
     "  \\end{array}",
     "}",
     "\\newcommand{\\cas}[5]{",
     "  \\begin{array}[t]{l}",
     "    \\text{case}\\;{ #1 }\\;\\text{of}\\;\\\\",
     "    \\;\\;\\;\\;\\text{inl}( #2 ) \\Rightarrow { #3 }\\\\",
     "    \\;\\;| \\;\\text{inr}( #4 ) \\Rightarrow { #5 }",
     "  \\end{array}",
     "}",
     "\\newcommand{\\casdots}[1]{\\text{case}\\;{ #1 }\\;\\text{of}\\;\\cdots}",
     "\\newcommand{\\inl}[2]{\\text{inl}( {#1},{#2} )}",
     "\\newcommand{\\inr}[2]{\\text{inr}( {#1},{#2} )}",
     "\\newcommand{\\fold}[2]{\\text{fold}({#1},{#2} )}",
     "\\newcommand{\\unfold}[2]{\\text{unfold}( {#1},{#2} )}",
     "\\begin{document}\n",
     "\\begin{preview}\n"]

latex_epilogue = "\\end{preview}\n\\end{document}\n"

latexprint_type One ctx = "1" 
latexprint_type (TV n) ctx = case ith n ctx of 
                               Just v -> v
                               Nothing -> "[TVar Not in CTX]"
latexprint_type ty@(And tya tyb) ctx = mwrap tya ty (latexprint_type tya ctx) 
                                         ++ "\\wedge " 
                                         ++ mwrap tyb ty (latexprint_type tyb ctx)
latexprint_type ty@(Or tya tyb) ctx = mwrap tya ty (latexprint_type tya ctx) 
                                        ++ "\\vee " 
                                        ++ mwrap tyb ty (latexprint_type tyb ctx)
latexprint_type ty@(Imp tya tyb) ctx = mwrap tya ty (latexprint_type tya ctx) 
                                         ++ " \\rightarrow " 
                                         ++ latexprint_type tyb ctx
latexprint_type tp@(All n ty) ctx = let n' = freshen n ctx 
                                    in "\\forall "++n'++" . "++ latexprint_type ty (n':ctx)
latexprint_type tp@(Nu n ty) ctx = let n' = freshen n ctx 
                                   in "\\nu "++n'++"." ++ latexprint_type ty (n':ctx)
latexprint_type tp@(Mu n ty) ctx = let n' = freshen n ctx 
                                   in "\\mu "++n'++"." ++ latexprint_type ty (n':ctx)

latexprint_term (V i) tc vc = case ith i vc of 
                                Just (n,ty) -> n
                                Nothing -> "[Var "++show i++" not in CTX]"
latexprint_term (F f) tc vc = f 
latexprint_term Unit tc vc = "()"
latexprint_term p@(App t s) tc vc = latexprint_term t tc vc ++"\\;" 
                                    ++ mwrap s p (latexprint_term s tc vc)
latexprint_term p@(TApp t ty) tc vc = mwrap t p (latexprint_term t tc vc) ++"\\;" 
                                      ++ "["++ latexprint_type ty tc ++"]"
latexprint_term p@(Pair t s) tc vc = "(" ++ latexprint_term t tc vc ++ ","
                                     ++ latexprint_term s tc vc ++ ")"
latexprint_term (Inl t ty) tc vc = "\\inl{"++latexprint_term t tc vc ++ "}{"
                                   ++ latexprint_type ty tc ++ "}"
latexprint_term (Inr t ty) tc vc = "\\inr{"++latexprint_term t tc vc ++ "}{"
                                   ++ latexprint_type ty tc ++ "}"
latexprint_term (Fold t ty) tc vc = "\\fold{"++latexprint_term t tc vc ++ "}{"
                                   ++ latexprint_type ty tc ++ "}"
latexprint_term (Unfold t ty) tc vc = "\\unfold{"++latexprint_term t tc vc ++ "}{"
                                      ++ latexprint_type ty tc ++ "}"
latexprint_term p@(Case t x r y s) tc vc = 
    "\\cas{"++ mwrap t p (latexprint_term t tc vc) ++ "}{"++x++"}{"
                ++ latexprint_term r tc ((x,One):vc) ++ "}{"++y++"}{"
                ++ latexprint_term s tc ((y,One):vc) ++ "}"
latexprint_term (Split t x y s) tc vc = 
    "\\spit{" ++ latexprint_term t tc vc ++ "}{"++x++"}{"++y++"}{"
                  ++ latexprint_term s tc ((y,One):(x,One):vc) ++"}"
latexprint_term p@(Lambda n ty t) tc vc = 
    let (vars,t') = strip_lambdas t
        lvars = map (\ (n,typ) -> (freshen n (map fst vc),typ)) ((n,ty):vars)
        vars' = reverse lvars
        vc' = vars' ++ vc
    in "\\lambda " ++ print_vars lvars tc ++ "." ++ latexprint_term t' tc vc'
latexprint_term p@(TLambda n t) tc vc = 
    let (vars,t') = strip_tlambdas t
        lvars = map (\ n -> freshen n tc) (n:vars)
        vars' = reverse lvars
        tc' = vars' ++ tc
    in "\\Lambda " ++ print_tvars lvars ++ "." ++ latexprint_term t' tc' vc

print_vars [] tc = ""
print_vars ((v,ty):[]) tc = "("++v ++ ":" ++ latexprint_type ty tc ++")"
print_vars ((v,ty):t) tc = "("++v ++ ":" ++ latexprint_type ty tc++")" ++","++print_vars t tc

print_tvars [] = ""
print_tvars (h:[]) = h
print_tvars (h:t) = h ++ "," ++ print_tvars t

strip_lambdas (Lambda n ty t) = 
    let (vars,t') = strip_lambdas t
    in ((n,ty):vars,t')
strip_lambdas t = ([],t)

strip_tlambdas (TLambda n t) = 
    let (vars,t') = strip_tlambdas t
    in (n:vars,t')
strip_tlambdas t = ([],t)

instance LatexPrint Term where 
    latexprint term = 
        latex_prologue
        ++ latexprint_term term [] []
        ++ latex_epilogue

instance LatexPrint PreProof where 
    latexprint pp = 
        latex_prologue
        ++ "{\n"
        ++ latexprint_pp pp
        ++ "\n\\DisplayProof}\n"
        ++ latex_epilogue

latexprint_pp (Pointer holds i []) = 
    "\\AxiomC{}"
    ++"\\RightLabel{\\scriptsize{Rec$^{"++show i++"}$}}" ++ "\n"
    ++ "\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (Pointer holds i (pp:[])) = 
    latexprint_pp pp++"\n"
    ++"\\RightLabel{\\scriptsize{Rec$^{"++show i++"}$}}" ++ "\n"
    ++ "\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (Pointer holds i (pp1:pp2:[])) = 
    latexprint_pp pp1++"\n"
    ++latexprint_pp pp2++"\n"
    ++"\\RightLabel{\\scriptsize{Rec$^{"++show i++"}$}}" ++ "\n"
    ++ "\\BinaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (Pointer holds i (pp1:pp2:pp3:_)) = 
    latexprint_pp pp1++"\n"
    ++latexprint_pp pp2++"\n"
    ++latexprint_pp pp3++"\n"
    ++"\\RightLabel{\\scriptsize{Rec$^{"++show i++"}$}}" ++ "\n"
    ++ "\\TrinaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (VarIntro holds) = 
    "\\AxiomC{}"
    ++"\\RightLabel{\\scriptsize{Var}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (FunIntro holds) =
    "\\AxiomC{}"
    ++"\\RightLabel{\\scriptsize{FunI}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (UnitIntro holds) = 
    "\\AxiomC{}"
    ++"\\RightLabel{\\scriptsize{UnitI}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (AllElim holds pp) = 
    latexprint_pp pp++ "\n"
    ++"\\RightLabel{\\scriptsize{AllE}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (AllIntro holds pp) = 
    latexprint_pp pp++ "\n"
    ++"\\RightLabel{\\scriptsize{AllI}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (ImpElim holds pp1 pp2) =
    latexprint_pp pp1 ++ "\n" 
    ++latexprint_pp pp2 ++ "\n"
    ++"\\RightLabel{\\scriptsize{ImpE}}" ++ "\n"
    ++"\\BinaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (ImpIntro holds pp) =
    latexprint_pp pp ++ "\n"
    ++"\\RightLabel{\\scriptsize{ImpI}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (AlphaIntro holds pp) = 
    latexprint_pp pp ++ "\n"
    ++"\\RightLabel{\\scriptsize{AlphaI}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (AlphaElim holds pp) = 
    latexprint_pp pp ++ "\n"
    ++"\\RightLabel{\\scriptsize{AlphaE}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (OrIntroL holds pp) =
    latexprint_pp pp ++ "\n"
    ++"\\RightLabel{\\scriptsize{OrIL}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (OrIntroR holds pp) =
    latexprint_pp pp ++ "\n"
    ++"\\RightLabel{\\scriptsize{OrIR}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (OrElim holds pp1 pp2 pp3) =
    latexprint_pp pp1 ++ "\n"
    ++latexprint_pp pp2 ++ "\n"
    ++latexprint_pp pp3 ++ "\n"   
    ++"\\RightLabel{\\scriptsize{OrElim}}" ++ "\n"
    ++"\\TrinaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (DeltaRule holds pp) =
    latexprint_pp pp ++ "\n"
    ++"\\RightLabel{\\scriptsize{$\\Delta$}}" ++ "\n"
    ++"\\UnaryInfC{$"++latexprint holds++"$}" ++ "\n"
latexprint_pp (AndIntro holds pp1 pp2) = 
    latexprint_pp pp1 ++ "\n"
    ++latexprint_pp pp2 ++ "\n"
    ++"\\RightLabel{\\scriptsize{AndI}}" ++ "\n"
    ++"\\BinaryInfC{$" ++ latexprint holds ++ "$}" ++ "\n"
latexprint_pp (AndElim holds pp1 pp2) = 
    latexprint_pp pp1 ++ "\n"
    ++latexprint_pp pp2 ++ "\n"
    ++"\\RightLabel{\\scriptsize{AndE}}" ++ "\n"
    ++"\\BinaryInfC{$" ++ latexprint holds ++ "$}" ++ "\n"
{-latexprint_pp d = 
    error $ "Unable to match derivation: "++show d -}

{-
instance LatexPrint TypeDerivationExn where
    latexprint (TDExn tc vc t rule) = 
        latexprint (TD (Holds ("Error!":tc) vc [] t One) rule)
    latexprint (Error s) = s

-}