-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for PrintFrappe.

module PrintFrappe where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsFrappe

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print AbsFrappe.Ident where
  prt _ (AbsFrappe.Ident i) = doc $ showString i
instance Print (AbsFrappe.Program' a) where
  prt i = \case
    AbsFrappe.Program _ stmts -> prPrec i 0 (concatD [prt 0 stmts])

instance Print (AbsFrappe.Stmt' a) where
  prt i = \case
    AbsFrappe.FnDef _ id_ args type_ block -> prPrec i 0 (concatD [doc (showString "func"), prt 0 id_, doc (showString ":"), doc (showString "("), prt 0 args, doc (showString ")"), doc (showString "->"), prt 0 type_, prt 0 block])
    AbsFrappe.Empty _ -> prPrec i 0 (concatD [doc (showString ";")])
    AbsFrappe.BStmt _ block -> prPrec i 0 (concatD [prt 0 block])
    AbsFrappe.Decl _ items type_ -> prPrec i 0 (concatD [prt 0 items, doc (showString ":"), prt 0 type_, doc (showString ";")])
    AbsFrappe.Ass _ leftsideass expr -> prPrec i 1 (concatD [prt 0 leftsideass, doc (showString "="), prt 0 expr, doc (showString ";")])
    AbsFrappe.SExp _ expr -> prPrec i 0 (concatD [prt 0 expr, doc (showString ";")])
    AbsFrappe.Incr _ id_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString "++"), doc (showString ";")])
    AbsFrappe.Decr _ id_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString "--"), doc (showString ";")])
    AbsFrappe.Ret _ expr -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expr, doc (showString ";")])
    AbsFrappe.VRet _ -> prPrec i 0 (concatD [doc (showString "return"), doc (showString ";")])
    AbsFrappe.Cond _ expr block -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])
    AbsFrappe.CondElse _ expr block1 block2 -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block1, doc (showString "else"), prt 0 block2])
    AbsFrappe.While _ expr block -> prPrec i 0 (concatD [doc (showString "while"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])
    AbsFrappe.Print _ exprs -> prPrec i 0 (concatD [doc (showString "print"), doc (showString "("), prt 0 exprs, doc (showString ")"), doc (showString ";")])

instance Print (AbsFrappe.Arg' a) where
  prt i = \case
    AbsFrappe.Arg _ id_ type_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 type_])
    AbsFrappe.ArgRef _ id_ type_ -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), doc (showString "@"), prt 0 type_])

instance Print [AbsFrappe.Arg' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsFrappe.Index' a) where
  prt i = \case
    AbsFrappe.Index _ expr -> prPrec i 0 (concatD [prt 0 expr])

instance Print [AbsFrappe.Index' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsFrappe.Block' a) where
  prt i = \case
    AbsFrappe.Block _ stmts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 stmts, doc (showString "}")])

instance Print [AbsFrappe.Stmt' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsFrappe.Item' a) where
  prt i = \case
    AbsFrappe.NoInit _ id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print [AbsFrappe.Item' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsFrappe.LeftSideAss' a) where
  prt i = \case
    AbsFrappe.LSAIdent _ id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print (AbsFrappe.ArgPass' a) where
  prt i = \case
    AbsFrappe.ArgByValue _ type_ -> prPrec i 0 (concatD [prt 0 type_])
    AbsFrappe.ArgByReference _ type_ -> prPrec i 0 (concatD [doc (showString "@"), prt 0 type_])

instance Print [AbsFrappe.ArgPass' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsFrappe.Type' a) where
  prt i = \case
    AbsFrappe.Int _ -> prPrec i 0 (concatD [doc (showString "int")])
    AbsFrappe.Str _ -> prPrec i 0 (concatD [doc (showString "string")])
    AbsFrappe.Bool _ -> prPrec i 0 (concatD [doc (showString "bool")])
    AbsFrappe.Void _ -> prPrec i 0 (concatD [doc (showString "void")])
    AbsFrappe.FunT _ argpasss type_ -> prPrec i 0 (concatD [doc (showString "("), prt 0 argpasss, doc (showString ")"), doc (showString "->"), prt 0 type_])

instance Print [AbsFrappe.Type' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsFrappe.Expr' a) where
  prt i = \case
    AbsFrappe.EVar _ id_ -> prPrec i 6 (concatD [prt 0 id_])
    AbsFrappe.ELitInt _ n -> prPrec i 6 (concatD [prt 0 n])
    AbsFrappe.ELitTrue _ -> prPrec i 6 (concatD [doc (showString "true")])
    AbsFrappe.ELitFalse _ -> prPrec i 6 (concatD [doc (showString "false")])
    AbsFrappe.EApp _ id_ exprs -> prPrec i 6 (concatD [prt 0 id_, doc (showString "("), prt 0 exprs, doc (showString ")")])
    AbsFrappe.EString _ str -> prPrec i 6 (concatD [printString str])
    AbsFrappe.Neg _ expr -> prPrec i 5 (concatD [doc (showString "-"), prt 6 expr])
    AbsFrappe.Not _ expr -> prPrec i 5 (concatD [doc (showString "!"), prt 6 expr])
    AbsFrappe.EMul _ expr1 mulop expr2 -> prPrec i 4 (concatD [prt 4 expr1, prt 0 mulop, prt 5 expr2])
    AbsFrappe.EAdd _ expr1 addop expr2 -> prPrec i 3 (concatD [prt 3 expr1, prt 0 addop, prt 4 expr2])
    AbsFrappe.ERel _ expr1 relop expr2 -> prPrec i 2 (concatD [prt 2 expr1, prt 0 relop, prt 3 expr2])
    AbsFrappe.EAnd _ expr1 expr2 -> prPrec i 1 (concatD [prt 2 expr1, doc (showString "&&"), prt 1 expr2])
    AbsFrappe.EOr _ expr1 expr2 -> prPrec i 0 (concatD [prt 1 expr1, doc (showString "||"), prt 0 expr2])
    AbsFrappe.ELambda _ args type_ block -> prPrec i 0 (concatD [doc (showString "lambda:"), doc (showString "("), prt 0 args, doc (showString ")"), doc (showString "->"), prt 0 type_, prt 0 block])

instance Print [AbsFrappe.Expr' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsFrappe.AddOp' a) where
  prt i = \case
    AbsFrappe.Plus _ -> prPrec i 0 (concatD [doc (showString "+")])
    AbsFrappe.Minus _ -> prPrec i 0 (concatD [doc (showString "-")])

instance Print (AbsFrappe.MulOp' a) where
  prt i = \case
    AbsFrappe.Times _ -> prPrec i 0 (concatD [doc (showString "*")])
    AbsFrappe.Div _ -> prPrec i 0 (concatD [doc (showString "/")])
    AbsFrappe.Mod _ -> prPrec i 0 (concatD [doc (showString "%")])

instance Print (AbsFrappe.RelOp' a) where
  prt i = \case
    AbsFrappe.LTH _ -> prPrec i 0 (concatD [doc (showString "<")])
    AbsFrappe.LE _ -> prPrec i 0 (concatD [doc (showString "<=")])
    AbsFrappe.GTH _ -> prPrec i 0 (concatD [doc (showString ">")])
    AbsFrappe.GE _ -> prPrec i 0 (concatD [doc (showString ">=")])
    AbsFrappe.EQU _ -> prPrec i 0 (concatD [doc (showString "==")])
    AbsFrappe.NE _ -> prPrec i 0 (concatD [doc (showString "!=")])
