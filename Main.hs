module Main where 

import Control.Monad.Omega
import Data.IORef 
import System.Cmd
import Lang
import Parse
import Program
import Eval
import Text.ParserCombinators.Parsec
import Super 
import Debug.Trace
import Exceptions 
import System.Directory
import System.IO
import Derivation
import Soundness 
import Reify
import Pretty
import Latex
import Loop
import Utils
import Generalise
import Data.List
import Normalise
import Data.Maybe
-- import qualified Control.Exception as E
import Hack
-- Test functions
-- import Conv
-- import Test

data Argv = Interactive
          | Batch [String]
          | Fail

data Command = Load String 
             | Super
             | Total Int
             | Quit 
             | Proof 
             | Display
             | Prog
             | Help
             | Unknown
             | Out
             | Up 
             | Term
             | Down Int
             | Check
             | Top
             | Norm
             | Unf
             | Reify
             | History
             | Candidates
             | Repeat Int
             | Generalise Int

default_search_depth = 2000

command str = let res = words str
              in case res of 
                   [":load",f] -> Load f
                   [":program"] -> Prog
                   [":proof"] -> Proof 
                   [":display"] -> Display
                   [":up"] -> Up
                   [":top"] -> Top
                   [":down"] -> Down 0
                   [":down",nstr] -> let ls = reads nstr :: [(Int,String)]
                                       in case ls of 
                                            [] -> Down 0
                                            (n,s):_ -> Down n
                   [":quit"] -> Quit
                   [":out"] -> Out
                   [":super"] -> Super                  
                   [":check"] -> Check
                   [":help"] -> Help
                   [":reify"] -> Reify
                   [":norm"] -> Norm
                   [":term"] -> Term
                   [":unfold"] -> Unf
                   [":history"] -> History
                   [":candidates"] -> Candidates
                   [":fold",nstr] -> let ls = reads nstr :: [(Int,String)]
                                      in case ls of 
                                           [] -> Unknown
                                           (n,s):_ -> Repeat n
                   [":generalise",nstr] -> let ls = reads nstr :: [(Int,String)]
                                           in case ls of 
                                                [] -> Unknown
                                                (n,s):_ -> Generalise n
                   [":total"] -> Total default_search_depth
                   [":total",nstr] -> let ls = reads nstr :: [(Int,String)]
                                      in case ls of 
                                           [] -> Total default_search_depth
                                           (n,s):_ -> Total n
                   _ -> Unknown

yesOrNo res = case words res of
                ["Yes"] -> True
                ["yes"] -> True
                ["Y"] -> True
                ["y"] -> True 
                _ -> False

help_message = "\n:load filename\t\tTo Load a file\n"++
               ":quit\t\t\tTo quit Poitin\n"++
               ":out [filename]\t\tOutput program to file\n"++
               ":proof [filename]\t\tOutput derivation to PDF file\n"++
               ":super\t\t\tSupercompile the current program\n"++
               ":reify\t\tReify term as program\n"++
               ":check\t\tCheck totality of the program\n"++
               ":total [n]\t\t\tSupercompile the current program searching for a provably total representative over n proofs\n"++
               ":help\t\t\tShow this message\n"++
               ":program\t\tTo print the current program\n"++ 
               ":down [n]\t\tDescend further into a term taking the n'th branch\n"++
               ":up\t\tAscend once step to the containing context term\n"++
               ":top\t\tAscend to the top level closed term\n"++
               ":norm\t\tNormalise the present term\n"++
               ":display\t\tShow pdf of derivation\n"++ 
               ":unfold\t\tUnfold the blocking term\n"++ 
               ":fold\t\tFold a term with a prior term\n"++
               ":term\t\tShow the present term"

showCandidates h ls = showCandidates' h ls 1
    where
      showCandidates' h [] n = ""
      showCandidates' h (h'@(Holds _ vctx tctx t _):rest) n = 
          if isJust (h' >- h)
          then show n ++ ". " ++ show_term t vctx tctx ++ "\n" ++ showCandidates' h rest (n+1)
          else showCandidates' h rest (n+1)
{-
main = readargs 

readargs :: IO ()
readargs = 
    do
      x <- getLine
      case (parse_argv x) of
  -}      

main = do   
  continue <- newIORef True
  program <- newIORef (Nothing :: Maybe Program)
  while (test continue id) 
        (do 
         putStr "Cocktail> "
         hFlush stdout
         x <- getLine
         case (command x) of 
           Load f -> do 
             x <- doesFileExist f
             if x 
               then do
                 res <- readFile f
                 case parsefile res of 
                   Left s -> do 
                            putStrLn ("Error: Could not parse term in file "++f++": "++ show s)
                            program #= Nothing
                   Right (fctx,t) -> do 
                          putStrLn ("Loading file: "++f)
                          case typeCheckFuns fctx of 
                            Left a -> do 
                              putStrLn "Functions are not type correct"
                              putStrLn a
                              program #= Nothing
                            Right _ -> do 
                              putStrLn "Functions are type correct"
                              case makeProof fctx [] [] t of 
                                Left a -> do 
                                  putStrLn a
                                  program #= Nothing
                                Right d -> do 
                                  putStrLn "Term is type correct" 
                                  program #= Just (Program [] d (f++".tot") "ouptput")
               else do 
                 putStrLn ("No such file: "++f) 
                 program #= Nothing
           Help -> putStrLn help_message
           Term -> do 
             p <- readIORef program
             case p of 
               Nothing -> putStrLn "No program loaded"
               Just p' -> putStrLn $ showProgramTerm p'
           Unknown -> putStrLn "Error: Could not parse command, type ':help' for a list of commands"
           Prog -> do 
             p <- readIORef program
             case p of 
               Nothing -> putStrLn "No program loaded"
               Just p -> putStrLn $ show p                      
           Super -> do 
             p <- readIORef program 
             case p of 
               Just p@(Program rt d i o) -> 
                   let proglist = do 
                            d <- runOmega $ super [] (proofSequent d)
                            return (do 
                                     (t', fctx') <- reify d []
                                     d' <- makeProof fctx' [] [] t' 
                                     return $ Program [] d' i o)
                   in foreach proglist (\ res -> 
                        case res of 
                          Left a -> do 
                            putStrLn a
                          Right p -> do
                            putStrLn $ show p
                            putStrLn $ "Would you like to keep searching? (y/n)"
                            hFlush stdout
                            x <- getLine
                            if yesOrNo x 
                              then return ()
                              else do 
                                program #= Just p
                                forbreak)
               _ -> putStrLn $ "No program loaded"                
           Total n -> do
             p <- readIORef program            
             case p of 
               Just p@(Program rt d i o) -> 
                   case filter isTotal $ take n $ runOmega $ super [] (proofSequent d) of
                     [] -> putStrLn $ "Unable to find a total proof" 
                     d:_ -> case (do
                                   (t',fctx') <- reify d []
                                   d <- makeProof fctx' [] [] t'
                                   return (Program [] d i o)) of 
                              Left a -> do
                                    putStrLn a
                                    program #= Just p
                              Right p -> do
                                    putStrLn $ show p
                                    program #= Just p
               _ -> putStrLn $ "No program loaded" 
           Check -> do 
             p <- readIORef program 
             case p of 
               Just p@(Program rt d i o) -> if isTotal d
                                            then putStrLn "Proof is total"
                                            else putStrLn "Proof is not total"
               _ -> putStrLn "No program loaded"
           Proof -> do 
             p <- readIORef program 
             case p of 
               Just (Program _  d _ o) -> do
                            let texfile = "/tmp/"++o++".tex"
                            writeFile texfile (latexprint d)
                            system $ "pdflatex "++o
                            return ()
               _ -> putStrLn $ "No derivation to output"
           Display -> do 
             p <- readIORef program 
             case p of 
               Just (Program _  d _ o) -> do
                            let texfile = "/tmp/"++o++".tex"
                            writeFile texfile (latexprint d)
                            system $ "pdflatex "++texfile
                            system $ "evince "++o++".pdf"          
                            return ()
               _ -> putStrLn $ "No derivation to output"
           Out -> do 
             p <- readIORef program
             case p of 
               Just prog@(Program _ _ progfile _) -> writeFile progfile (show prog)
               _ -> putStrLn $ "No program to output"
           Up -> do 
             p <- readIORef program
             case p of 
               Just (Program rt d f1 f2) ->
                   case position (up rt) d of
                     Nothing -> putStrLn "No term to move up in."
                     Just _ -> do
                            let prog = Program (up rt) d f1 f2
                            program #= (Just prog)
                            putStrLn $ showProgramTerm prog
               _ -> putStrLn "No program to move up in."
           Down i -> do 
             p <- readIORef program 
             case p of 
               Just (Program rt d f1 f2) -> 
                   case (do 
                          proof <- maybe (Left "No term to move down in, at this index") return (position rt d)
                          tag <- maybe (Left "Unable to move down in proof") return (down i proof)
                          return $ Program (rt++[tag]) d f1 f2) of
                     Left s -> putStrLn s
                     Right p -> do
                            program #= (Just p)
                            putStrLn $ showProgramTerm p
               _ -> putStrLn "No Program to move down in."
           Unf -> do 
             p <- readIORef program 
             case p of 
               Just (Program rt d f1 f2) -> 
                    case position rt d of 
                      Nothing -> putStrLn "Corrupted path."
                      Just proof -> do  
                            let h = maybe (proofSequent proof) id (unfold $ proofSequent proof)
                            case holdsToProof h of
                              Left s -> putStrLn s
                              Right p' -> 
                                  case replace rt (DeltaRule (proofSequent proof) p') d of 
                                    Nothing -> putStrLn "Unable to unfold program"
                                    Just d' -> do 
                                         let p = Program (rt++[DeltaTag]) d' f1 f2
                                         program #= (Just p)
                                         putStrLn $ showProgramTerm p
               _ -> putStrLn "No Program to unfold."
           Repeat n -> do 
             p <- readIORef program 
             case (do 
                    (Program rt d f1 f2) <- maybe (Left "No program loaded") return p
                    d' <- maybe (Left "Corrupted path") return (position rt d)
                    pa <- maybe (Left "Corrupted path") return (path rt d)
                    let h = proofSequent d'
                    h' <- maybe (Left "Index refers beyond the bounds of history.") return (ith (n-1) (reverse pa))
                    s <- maybe (Left (let (Holds _ vctx tctx t _) = h 
                                          (Holds _ vctx' tctx' t' _ ) = h' 
                                      in show_term t vctx tctx ++ "\n\nis not an instance of\n\n"++ show_term t' vctx' tctx'))
                         return (h' >- h)
                    ds <- mapM (\ t -> do                  
                                  let (Holds fctx vctx tctx _ _) =  h
                                  makeProof fctx vctx tctx t) (map snd s)
                    d' <- maybe (Left "Failure to replace in path.") return (replace rt (Pointer h n ds) d)
                    return $ Program rt d' f1 f2) of
                Left s -> putStrLn s
                Right p'@(Program _ d' _ _) -> do
                            program #= (Just p')
                            putStrLn $ showProgramTerm p'         
           History -> do 
              p <- readIORef program 
              case p of 
                Just (Program rt d f1 f2) -> 
                    case path rt d of 
                      Nothing -> putStrLn "No associated Path"
                      Just pa -> putStrLn $ showHistory (reverse pa)
                Nothing -> putStrLn "No Program to display history for."
           Candidates -> do 
              p <- readIORef program 
              case p of 
                Just (Program rt d f1 f2) -> 
                    either putStrLn putStrLn (do 
                                               pa <- maybe (fail "No associated Path") return (path rt d)
                                               d' <- maybe (fail "Corrupted path") return (position rt d)
                                               let h = proofSequent d'
                                               return $ showCandidates h (reverse pa))
                Nothing -> putStrLn "No Program to display history for."
           Generalise n -> do 
             p <- readIORef program 
             case (do
                    (Program rt d f1 f2) <- maybe (fail "Corrputed path") return p 
                    d' <- maybe (fail "Corrupted path") return (position rt d)
                    pa <- maybe (fail "Unable to construct path") return (path rt d)
                    h' <- maybe (fail "No such element of the history") return (ith (n-1) (reverse pa))
                    let h = proofSequent d' 
                    r <- generalisedApplication h h'
                    -- rt' <- maybe (fail "No such initial segment of path") return (ith (n-1) (inits rt))
                    d'' <- maybe (fail "Unable to replace in path with generalisation.") return (replace rt r d)
                    return $ Program rt d'' f1 f2) of 
                Right p'@(Program _ d' _ _)  -> do
                             program #= (Just p')
                             putStrLn $ showProgramTerm p'
                Left s -> putStrLn s
           Norm -> do 
             p <- readIORef program 
             case (do
                    (Program rt d f1 f2) <- maybe (fail "Corrputed path") return p 
                    d' <- maybe (fail "Corrupted path") return (position rt d)
                    let h = proofSequent d'
                    let h' = sequentNorm h                        
                    r <- either (fail "Unnormalisable") return (holdsToProof h')
                    d'' <- maybe (fail "Unable to replace in path with generalisation.") return (replace rt r d)
                    return $ Program rt d'' f1 f2) of 
                Right p'@(Program _ d' _ _)  -> do
                             program #= (Just p')
                             putStrLn $ showProgramTerm p'
                Left s -> putStrLn s
           Top -> do 
             p <- readIORef program 
             case p of 
               Just (Program rt d f1 f2) -> do
                            let prog = Program [] d f1 f2
                            program #= (Just prog)
                            putStrLn $ showProgramTerm prog
               _ -> putStrLn "No Program to norm."
           Reify -> do 
             p <- readIORef program 
             case p of 
               Just p@(Program rt d i o) -> 
                   case (do 
                          (t', fctx') <- reify d []
                          d' <- makeProof fctx' [] [] t' 
                          return $ Program [] d' i o) of 
                     Left s -> putStrLn s
                     Right prog -> do 
                            program #= (Just prog) 
                            putStrLn $ showProgramTerm prog
           Quit -> continue #= False)
