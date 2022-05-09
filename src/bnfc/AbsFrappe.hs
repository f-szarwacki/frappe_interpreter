-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language Frappe.

module AbsFrappe where

import Prelude (Integer, String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String

type Program = Program' BNFC'Position
data Program' a = Program a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Stmt = Stmt' BNFC'Position
data Stmt' a
    = FnDef a Ident [Arg' a] (Type' a) (Block' a)
    | Empty a
    | BStmt a (Block' a)
    | Decl a [Item' a] (Type' a)
    | Ass a (LeftSideAss' a) (Expr' a)
    | SExp a (Expr' a)
    | Incr a Ident
    | Decr a Ident
    | Ret a (Expr' a)
    | VRet a
    | Cond a (Expr' a) (Block' a)
    | CondElse a (Expr' a) (Block' a) (Block' a)
    | While a (Expr' a) (Block' a)
    | Print a [Expr' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Arg = Arg' BNFC'Position
data Arg' a = Arg a Ident (Type' a) | ArgRef a Ident (Type' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Index = Index' BNFC'Position
data Index' a = Index a (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Block = Block' BNFC'Position
data Block' a = Block a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Item = Item' BNFC'Position
data Item' a = NoInit a Ident | NoInitArr a Ident [Index' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type LeftSideAss = LeftSideAss' BNFC'Position
data LeftSideAss' a
    = LSAIdent a Ident | LSAArray a Ident [Index' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a
    = Int a
    | Str a
    | Bool a
    | Void a
    | FunT a [Type' a] (Type' a)
    | Array a [Index' a] (Type' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Expr = Expr' BNFC'Position
data Expr' a
    = EVar a Ident
    | EArray a Ident [Index' a]
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | EApp a Ident [Expr' a]
    | EString a String
    | Neg a (Expr' a)
    | Not a (Expr' a)
    | EMul a (Expr' a) (MulOp' a) (Expr' a)
    | EAdd a (Expr' a) (AddOp' a) (Expr' a)
    | ERel a (Expr' a) (RelOp' a) (Expr' a)
    | EAnd a (Expr' a) (Expr' a)
    | EOr a (Expr' a) (Expr' a)
    | ELambda a [Arg' a] (Type' a) (Block' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AddOp = AddOp' BNFC'Position
data AddOp' a = Plus a | Minus a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = Times a | Div a | Mod a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RelOp = RelOp' BNFC'Position
data RelOp' a = LTH a | LE a | GTH a | GE a | EQU a | NE a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    Program p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    FnDef p _ _ _ _ -> p
    Empty p -> p
    BStmt p _ -> p
    Decl p _ _ -> p
    Ass p _ _ -> p
    SExp p _ -> p
    Incr p _ -> p
    Decr p _ -> p
    Ret p _ -> p
    VRet p -> p
    Cond p _ _ -> p
    CondElse p _ _ _ -> p
    While p _ _ -> p
    Print p _ -> p

instance HasPosition Arg where
  hasPosition = \case
    Arg p _ _ -> p
    ArgRef p _ _ -> p

instance HasPosition Index where
  hasPosition = \case
    Index p _ -> p

instance HasPosition Block where
  hasPosition = \case
    Block p _ -> p

instance HasPosition Item where
  hasPosition = \case
    NoInit p _ -> p
    NoInitArr p _ _ -> p

instance HasPosition LeftSideAss where
  hasPosition = \case
    LSAIdent p _ -> p
    LSAArray p _ _ -> p

instance HasPosition Type where
  hasPosition = \case
    Int p -> p
    Str p -> p
    Bool p -> p
    Void p -> p
    FunT p _ _ -> p
    Array p _ _ -> p

instance HasPosition Expr where
  hasPosition = \case
    EVar p _ -> p
    EArray p _ _ -> p
    ELitInt p _ -> p
    ELitTrue p -> p
    ELitFalse p -> p
    EApp p _ _ -> p
    EString p _ -> p
    Neg p _ -> p
    Not p _ -> p
    EMul p _ _ _ -> p
    EAdd p _ _ _ -> p
    ERel p _ _ _ -> p
    EAnd p _ _ -> p
    EOr p _ _ -> p
    ELambda p _ _ _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    Plus p -> p
    Minus p -> p

instance HasPosition MulOp where
  hasPosition = \case
    Times p -> p
    Div p -> p
    Mod p -> p

instance HasPosition RelOp where
  hasPosition = \case
    LTH p -> p
    LE p -> p
    GTH p -> p
    GE p -> p
    EQU p -> p
    NE p -> p

