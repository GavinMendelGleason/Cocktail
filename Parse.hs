module Parse where 

import Lang
import Eval
import Data.List 
import Program

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Perm

import Data.Char

langDef = emptyDef
         { commentStart   = "/*"
         , commentEnd     = "*/"
         , commentLine    = ""
         , nestedComments = True
         , identStart     = lower <|> upper
         , identLetter    = do 
             alphaNum <|> oneOf "_'"
         , reservedNames  = ["case","of","where","split","as","in","end","inl","inr","fold","unfold","mu","nu","all","1","U"]
         , reservedOpNames= ["%","#","=>","|","(",")",".",";","[","]"]
         , caseSensitive  = True
         }

lexer = P.makeTokenParser langDef

whiteSpace= P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer
decimal   = P.decimal lexer

file = do 
  t <- term
  fl <- (do 
          reserved "where"
          many fun) <|> return []
  return $ (fl,t)

fun = do 
  f <- identifier 
  symbol ":" 
  ty <- typ
  symbol "="
  t <- term 
  symbol ";"
  return (f,t,ty)

term = do 
  try appT
  <|> try app
  <|> simple_term

simple_term = do
  var
  <|> unit
  <|> inr
  <|> inl
  <|> fold
  <|> unf
  <|> split      
  <|> cas 
  <|> lam
  <|> tlam
  <|> try pair -- Should factor this with grouping below
  <|> (do 
        symbol "("
        t <- term
        symbol ")"
        return t)

appT = do 
  base <- simple_term
  res <- many1 (do 
                 symbol "["
                 t <- typ
                 symbol "]"
                 return t)
  return (foldl TApp base res)

app = do 
  res <- many simple_term 
  case res of 
    [] -> fail "No applications"
    (h:t) -> return (foldl App h t)

var = do 
  i <- identifier
  return $ F i

inl = do 
  reserved "inl"
  symbol "("
  t <- term
  symbol ","
  ty <- typ 
  symbol ")"
  return (Inl t ty)

inr = do 
  reserved "inr"
  symbol "("
  t <- term
  symbol ","
  ty <- typ
  symbol ")"
  return $ Inr t ty

pair = do 
  symbol "(" 
  t <- term 
  symbol "," 
  s <- term 
  symbol ")"
  return $ Pair t s

fold = do 
  reserved "fold"
  symbol "("
  t <- term 
  symbol ","
  ty <- typ
  symbol ")"
  return $ Fold t ty

unf = do 
  reserved "unfold"
  symbol "("
  t <- term 
  symbol ","
  ty <- typ
  symbol ")"
  return $ Unfold t ty

unit = do 
  reserved "U" 
  return $ Unit

lam = do 
  symbol "\\" 
  vl <- many1 (do 
                i <- identifier 
                symbol ":"
                ty <- typ 
                return (i,ty))
  symbol "."
  t <- term
  return $ makeLam vl t

tlam = do 
  symbol "/\\"
  vl <- many1 identifier 
  symbol "." 
  t <- term 
  return $ makeTLam vl t

cas = do 
  reserved "case" 
  t <- term 
  reserved "of" 
  symbol "{"
  reserved "inl"
  symbol "("
  x <- identifier 
  symbol ")"
  symbol "=>" 
  l <- term
  symbol "|"
  reserved "inr"
  symbol "("
  y <- identifier 
  symbol ")"
  symbol "=>" 
  r <- term
  symbol "}"
  return $ makeCase t x l y r

split = do 
  reserved "split" 
  t <- term 
  reserved "as" 
  symbol "("
  x <- identifier 
  symbol ","
  y <- identifier
  symbol ")"
  reserved "in"
  symbol "{"
  r <- term
  symbol "}"
  return $ makeSplit t x y r

prodOp = do 
  symbol "*" 
  prod
prod = do 
         ty1 <- baseType         
         (do 
           ty2 <- prodOp
           return $ And ty1 ty2
          <|> 
          do 
            return ty1)

funcOp = do 
  symbol "->" 
  func
func = do   
         ty1 <- prod
         (do 
           ty2 <- funcOp
           return $ Imp ty1 ty2
          <|>
          do 
            return ty1)

orTOp = do 
  symbol "+" 
  orT
orT = do 
    ty1 <- func
    (do 
      ty2 <- orTOp
      return $ Or ty1 ty2
     <|>
     do return ty1)

mu = do 
  reserved "mu" 
  is <- many1 identifier 
  symbol "."
  ty <- typ 
  return $ makeMu is ty

nu = do 
  reserved "nu"
  is <- many1 identifier
  symbol "." 
  ty <- typ 
  return $ makeNu is ty

allT = do 
  reserved "\\-/" 
  is <- many1 identifier
  symbol "." 
  ty <- typ 
  return $ makeAll is ty

tvar = do 
  i <- identifier
  return $ FT i

one = do 
  reserved "1"
  return One

baseType = do
  tvar
  <|> one
  <|> allT
  <|> mu 
  <|> nu 
  <|> (do 
        symbol "("
        t <- typ
        symbol ")"
        return t)
   
typ = do 
  orT
  <|> baseType

{-
typSyn = do 
  i <- identifier 
  args <- many identifier
  symbol "=" 
  ty <- typ 
  return (i,args,ty)
-} 

parsetype input = parse typ "(ERROR)" input

parsetype_err input = case (parsetype input) of 
                        Right l -> l 
                        Left s -> error "Unable to parse type"

parseterm input = parse term "(ERROR)" input

parseterm_err input = case (parseterm input) of 
                        Right l -> l 
                        Left s -> error "Unable to parse term"

parsefile input = parse file "(ERROR)" input

parsefile_err input = case (parsefile input) of 
                        Right l -> l
                        Left s -> error "Unable to parse file"


parsefuns input = parse (many fun) "(ERROR)" input 
parsefuns_err input = case parsefuns input of 
                        Right l -> l 
                        Left s -> error "Unable to parse file"




