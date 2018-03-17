module Program where 

import Lang
import Derivation
import Soundness
import Pretty 

type ProgramOutFile = String
type PDFOutFile = String
data Program = Program [RuleTag] PreProof ProgramOutFile PDFOutFile

-- makeProgram fl t = Program fl t [] Nothing Nothing "output.pot" "ouptput"

instance Show Program where 
    show (Program rt d _ _) = 
        let oh@(Holds fctx _ _ t ty) = proofSequent d                                       
        in if null rt 
           then show_term t [] [] ++ "\n\nwhere\n\n" ++ (concatMap (\ (f,t,ty) -> f++" : " ++ show_type ty [] ++" = \n"
                                                                                  ++show_term t [] []++";\n\n") fctx)
           else case position rt d of 
                  Nothing -> show_term t [] [] ++ "\n\nwhere\n\n" ++ (concatMap (\ (f,t,ty) -> f++" : " ++ show_type ty [] ++" = \n"
                                                                                               ++show_term t [] []++";\n\n") fctx)
                  Just h -> show h ++ " in " ++ show oh
                                   ++ "\n\nwhere\n\n" ++ (concatMap (\ (f,t,ty) -> f++" : " ++ show_type ty [] ++" = \n"
                                                                                   ++show_term t [] []++";\n\n") fctx)

showProgramTerm (Program rt d _ _) = 
    let oh@(Holds fctx _ _ t ty) = proofSequent d                                       
    in let proof = maybe d id (position rt d)
       in case proof of 
            DeltaRule h proof' -> 
                let (Holds _ vctx tctx t _) = proofSequent proof
                    (Holds _ vctx' tctx' t' _) = proofSequent proof' 
                in show_term t vctx tctx ++ "\n\n  ~>\n\n    " ++ show_term' t' vctx' tctx' 4
            Pointer h i l -> 
                let (Holds _ vctx tctx t _) = proofSequent proof
                    hs = map proofSequent l
                in "#" ++ show i ++ " " ++ show_term t vctx tctx ++ "\n\n" ++ showHistory hs
            _ -> let (Holds _ vctx tctx t _) = proofSequent proof
                 in show_term t vctx tctx