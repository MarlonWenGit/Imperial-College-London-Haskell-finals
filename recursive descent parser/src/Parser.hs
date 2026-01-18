module Parser where

import Types
import Lexer
import Examples

import Data.Maybe

------------------------------------------------------------------------------
-- Given...

showToken :: Token -> String
showToken (Ident v) = v
showToken (Nat v) = show v
showToken WhileTok = "while"
showToken t = [head [c | (c, t') <- tokenTable, t == t']]

printParse :: String -> IO ()
printParse input = either printError printOK (parse input)
  where
    printOK prog = putStrLn "Parse successful..." >> print prog
    printError err = putStr "Parse error: " >> printError' err
    printError'' t s = putStrLn (s ++ " expected, but " ++
                                 maybe "nothing" showToken t ++ " found")
    printError' (BadChar c) = do putStr "Unrecognised character: "
                                 putStrLn [c]
    printError' (Unexpected t t') = printError'' t (showToken t')
    printError' (StmtNotFound t) = printError'' t "Statement"
    printError' (ExprNotFound t) = printError'' t "Expression"
    printError' (IntNotFound t) = printError'' t "Integer literal"
    printError' (UnparsedInput toks) = putStrLn ("Unparsed input: " ++
                                                 unwords (map showToken toks))

------------------------------------------------------------------------------

-- Given...
mHead :: [a] -> Maybe a
mHead (x : _) = Just x
mHead _ = Nothing

checkTok :: Token -> [Token] -> Either Error [Token]
checkTok t' [] = Left (Unexpected Nothing t')
checkTok t' (t:ts)
  | t' == t   = Right ts
  | otherwise = Left (Unexpected (Just t) t')

parseAtom :: Parser Expr
parseAtom ((Ident s):ts) = Right (ts, Var s)
parseAtom ((Nat n):ts) = Right (ts, Val n)
parseAtom (Minus:(Nat n):ts) = Right (ts, Val (negate n))
parseAtom (Minus:ts) = Left (IntNotFound (mHead ts))
parseAtom (LParen:ts) = do
  (ts', e) <- parseExpr ts
  ts'' <- checkTok RParen ts'
  return (ts'', e)
parseAtom ts = Left (ExprNotFound (mHead ts))

parseOp :: (Expr -> Expr -> Expr) -> Token -> Parser Expr -> Parser Expr
parseOp op id parser ts = do 
  (ts', t) <- parser ts
  parseOp' op id t ts'
  where 
    parseOp' :: (Expr -> Expr -> Expr) -> Token -> Expr -> Parser Expr
    parseOp' op id t ts@(id':toks) 
      | id == id' = do
                  (toks', x) <- parser toks
                  parseOp' op id (op t x) toks'
    parseOp' op id t toks = Right (toks, t)

parseTerm :: Parser Expr
parseTerm = parseOp Mul Times parseAtom

parseExpr :: Parser Expr
parseExpr = parseOp Add Plus parseTerm

parseStmt :: Parser Stmt
parseStmt ((Ident s):Eq:ts) = do 
  (ts', e) <- parseExpr ts
  return (ts', Asgn s e)
parseStmt (WhileTok:ts) = do
  (ts', c) <- parseExpr ts
  ts'' <- checkTok LBrace ts'
  (ts''', b) <- parseBlock ts''
  ts'''' <- checkTok RBrace ts'''
  return (ts'''', While c b)
parseStmt ts = Left (StmtNotFound (mHead ts))

parseBlock :: Parser Block
parseBlock = parseBlock' []
  where 
    parseBlock' :: Block -> Parser Block
    parseBlock' acc ts = do
      (ts', s) <- parseStmt ts
      let acc' = s : acc
      case ts' of
        []          -> Right ([], reverse acc')
        Semi : ts'' -> parseBlock' acc' ts''
        _           -> Right (ts', reverse acc')

parse :: String -> Either Error Program
parse input = do 
  ts <- tokenise input
  (ts', b) <- parseBlock ts
  case ts' of
    [] -> Right b
    _ -> Left (UnparsedInput ts')
