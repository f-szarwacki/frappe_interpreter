{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE TypeSynonymInstances #-}


module TypeChecker where

import AbsFrappe
import PrintFrappe

import Data.String
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import qualified Data.Map as M

type TypeCheckError = String
type Position = BNFC'Position -- Maybe (Int, Int)
type TypeMap = M.Map Ident TType

makeError :: Position -> String -> TypeCheckError
makeError pos errorString = (case pos of
  Just (row, column) -> "Error at row " ++ show row ++ ", column " ++ show column ++ ": "
  Nothing -> "Error: ") ++ errorString ++ "."

type TypeCheckerMonad = ExceptT TypeCheckError (ReaderT (Maybe TType) (StateT TypeMap Identity))

typeCheck :: Program -> TypeCheckerMonad ()
typeCheck (Program _ stmts) = forM_ stmts typeCheckStmt

typeCheckStmt :: Stmt -> TypeCheckerMonad ()

addIdTypePair :: Position -> Ident -> TType -> TypeCheckerMonad ()
addIdTypePair pos id t = case t of
  TVoid -> throwError $ makeError pos "cannot declare variable as void"
  _ -> modify (M.insert id t)

getArgTType :: Arg -> (ArgWay, TType)
getArgTType (Arg _ _ t) = (ByValue, getType t)
getArgTType (ArgRef _ _ t) = (ByReference, getType t)

typeCheckStmt (FnDef pos ident args returnType (Block _ stmts)) = do
  savedState <- get
  forM_ args (\arg-> case arg of
    Arg pos id t -> addIdTypePair pos id (getType t)
    ArgRef pos id t -> addIdTypePair pos id (getType t))
  -- Function should be visible inside itself to allow recurrent call.
  addIdTypePair pos ident (TFun (map getArgTType args) (getType returnType))
  local (\_-> Just $ getType returnType) (forM_ stmts typeCheckStmt)
  put savedState
  -- The argument variables are going out of scope, but the function itself has to be readded.
  addIdTypePair pos ident (TFun (map getArgTType args) (getType returnType))

typeCheckStmt (Empty pos) = return ()
typeCheckStmt (BStmt pos (Block _ stmts)) = do
  savedState <- get
  forM_ stmts typeCheckStmt
  put savedState

typeCheckStmt (Decl pos items t) = do
  forM_ items (\item -> case item of
    NoInit pos id -> addIdTypePair pos id (getType t)
    NoInitArr pos id idxs -> error "not implemented")

typeCheckStmt (Ret pos expr) = do
  typeRequired <- ask
  typeInferred <- typeCheckExpr expr
  case typeRequired of
    Nothing -> throwError $ makeError pos "unexpected return statement"
    Just t -> if doTTypesMatch t typeInferred then return () else throwError $ makeError pos ("mismatch between type declared: " ++ show t ++ ", and type returned: " ++ show typeInferred)

typeCheckStmt (VRet pos) = do
  typeRequired <- ask
  case typeRequired of
    Nothing -> throwError $ makeError pos "unexpected return statement"
    Just TVoid -> return ()
    Just t -> throwError $ makeError pos ("function should return: " ++ show t ++ ", but it returns void")

typeCheckStmt (Ass pos lsa expr) = do
  case lsa of
    LSAIdent _ id -> do
      exprType <- typeCheckExpr expr
      maybetype <- gets (M.lookup id)
      case maybetype of
        Nothing -> throwError $ makeError pos "cannot assign to undeclared variable"
        Just varType -> if doTTypesMatch exprType varType
          then return ()
          else throwError $ makeError pos ("variable is declared as of type: " ++ show varType ++ ", it cannot be assigned a value of type: " ++ show exprType)
    LSAArray _ id idxs -> error "not implemented"

typeCheckStmt (SExp _ expr) = do
  typeCheckExpr expr
  return ()

typeCheckStmt (Incr pos id) = do
  maybetype <- gets (M.lookup id)
  case maybetype of
    Nothing -> throwError $ makeError pos "variable not declared"
    Just TInt -> return ()
    Just _ -> throwError $ makeError pos "variable is not an integer, it cannot be incremented"

typeCheckStmt (Decr pos id) = do
  maybetype <- gets (M.lookup id)
  case maybetype of
    Nothing -> throwError $ makeError pos "variable not declared"
    Just TInt -> return ()
    Just _ -> throwError $ makeError pos "variable is not an integer, it cannot be decremented"

typeCheckStmt (Cond pos expr (Block _ stmts)) = do
  conditionType <- typeCheckExpr expr
  case conditionType of
    TBool -> return ()
    _ -> throwError $ makeError pos "condition expression must have a boolean value"
  savedState <- get
  forM_ stmts typeCheckStmt
  put savedState

typeCheckStmt (CondElse pos expr (Block _ stmts1) (Block _ stmts2)) = do
  conditionType <- typeCheckExpr expr
  case conditionType of
    TBool -> return ()
    _ -> throwError $ makeError pos "condition expression must have a boolean value"
  savedState <- get
  forM_ stmts1 typeCheckStmt
  put savedState
  savedState <- get
  forM_ stmts2 typeCheckStmt
  put savedState

typeCheckStmt (While pos expr (Block _ stmts)) = do
  conditionType <- typeCheckExpr expr
  case conditionType of
    TBool -> return ()
    _ -> throwError $ makeError pos "condition expression must have a boolean value"
  savedState <- get
  forM_ stmts typeCheckStmt
  put savedState

typeCheckStmt (Print pos exprs) = do
  forM_ exprs (\expr -> do
    toPrintType <- typeCheckExpr expr
    case toPrintType of
      TInt -> return ()
      TString -> return ()
      TBool -> return ()
      t -> throwError $ makeError pos ("cannot print value of type: " ++ show t))

-- Checking types of all operations and returning type of expression.
typeCheckExpr :: Expr -> TypeCheckerMonad TType
typeCheckExpr expr = case expr of
  EVar pos id -> do
    maybetype <- gets (M.lookup id)
    case maybetype of
      Nothing -> throwError $ makeError pos "variable not declared"
      Just t -> return t
  ELitInt pos _ -> return TInt
  ELitTrue pos -> return TBool
  ELitFalse pos -> return TBool
  EString pos _ -> return TString
  Neg pos expr -> do
    exprType <- typeCheckExpr expr
    case exprType of
      TInt -> return TInt
      _ -> throwError $ makeError pos "cannot integer negate type " ++ show exprType
  Not pos expr -> do
    exprType <- typeCheckExpr expr
    case exprType of
      TBool -> return TBool
      _ -> throwError $ makeError pos "cannot boolean negate type " ++ show exprType
  EMul pos expr1 mulOp expr2 -> do
    exprType1 <- typeCheckExpr expr1
    case exprType1 of
      TInt -> do
        exprType2 <- typeCheckExpr expr2
        case exprType2 of
          TInt -> return TInt
          _ -> throwError $ makeError pos ("cannot perform " ++ printTree mulOp ++ " on type " ++ show exprType2)
      _ -> throwError $ makeError pos ("cannot perform " ++ printTree mulOp ++ " on type " ++ show exprType1)
  EAdd pos expr1 addOp expr2 -> do
    exprType1 <- typeCheckExpr expr1
    case exprType1 of
      TInt -> do
        exprType2 <- typeCheckExpr expr2
        case exprType2 of
          TInt -> return TInt
          _ -> throwError $ makeError pos ("cannot perform " ++ printTree addOp ++ " on type " ++ show exprType2)
      _ -> throwError $ makeError pos ("cannot perform " ++ printTree addOp ++ " on type " ++ show exprType1)
  ERel pos expr1 relOp expr2 -> do
    exprType1 <- typeCheckExpr expr1
    case exprType1 of
      TInt -> do
        exprType2 <- typeCheckExpr expr2
        case exprType2 of
          TInt -> return TBool
          _ -> throwError $ makeError pos ("cannot perform " ++ printTree relOp ++ " on type " ++ show exprType2)
      _ -> throwError $ makeError pos ("cannot perform " ++ printTree relOp ++ " on type " ++ show exprType1)
  EAnd pos expr1 expr2 -> do
    exprType1 <- typeCheckExpr expr1
    case exprType1 of
      TBool -> do
        exprType2 <- typeCheckExpr expr2
        case exprType2 of
          TBool -> return TBool
          _ -> throwError $ makeError pos ("cannot perform && on type " ++ show exprType2)
      _ -> throwError $ makeError pos ("cannot perform && on type " ++ show exprType1)
  EOr pos expr1 expr2 -> do
    exprType1 <- typeCheckExpr expr1
    case exprType1 of
      TBool -> do
        exprType2 <- typeCheckExpr expr2
        case exprType2 of
          TBool -> return TBool
          _ -> throwError $ makeError pos ("cannot perform || on type " ++ show exprType2)
      _ -> throwError $ makeError pos ("cannot perform || on type " ++ show exprType1)
  
  ELambda pos args returnType (Block _ stmts) -> do
    savedState <- get
    forM_ args (\arg-> case arg of
      Arg pos id t -> addIdTypePair pos id (getType t)
      ArgRef pos id t -> addIdTypePair pos id (getType t))
    local (\_-> Just $ getType returnType) (forM_ stmts typeCheckStmt)
    put savedState
    -- Return defined function type.
    return (TFun (map getArgTType args) (getType returnType))

  EArray pos id idxs -> error "not implemented"

  EApp pos id exprs -> do
    maybetype <- gets (M.lookup id)
    case maybetype of
      Nothing -> throwError $ makeError pos "function is not declared"
      Just t -> case t of
        TFun argTypes returnType -> do
          checkArgsType pos argTypes exprs
          return returnType
        _ -> throwError $ makeError pos ("variable is not a function (it is of type: " ++ show t ++ "), it cannot be used as such")

-- Checking if number and types of expressions given match those declared.
checkArgsType :: Position -> [(ArgWay, TType)] -> [Expr] -> TypeCheckerMonad ()
checkArgsType pos argTypes exprs = do
  when (length argTypes /= length exprs) (throwError $ makeError pos ("number of arguments required: " ++ show (length argTypes) ++ ", and given: " ++ show (length exprs) ++ ", does not match"))
  forM_ (zip argTypes exprs) (\(argType, expr) -> do
    case argType of
      (ByReference, t) -> case expr of
        EVar _ _ -> return ()
        _ -> throwError $ makeError pos "cannot use a non-variable expression as argument passed by reference"
      _ -> return ())
  forM_ (zip argTypes exprs) (\(argType, expr) -> do
    typeInferred <- typeCheckExpr expr
    when (not $ doTTypesMatch typeInferred (snd argType)) (throwError $ makeError pos ("type in function definition and application does not match. Expected: " ++ show (snd argType) ++ ", got: " ++ show typeInferred)))
  
-- Way of passing an argument.
data ArgWay = ByValue | ByReference deriving (Eq, Ord, Show, Read)

data TType = TInt
    | TString
    | TBool
    | TVoid
    | TFun [(ArgWay, TType)] TType
    | TArray [Integer] TType
  deriving (Eq, Ord, Read)

instance Show TType where
  show t = case t of
    TInt -> "int"
    TString -> "string"
    TBool -> "bool"
    TVoid -> "void"
    TFun argTypes returnType -> "(" ++ (intercalate ", " (map (\(argWay, t) -> (case argWay of
      ByValue -> ""
      ByReference -> "@") ++ show t) argTypes)) ++ ") -> " ++ show returnType 
    TArray _ _ -> error "not implemented"

getType :: Type -> TType
getType t = case t of
  Int a -> TInt
  Str a -> TString
  Bool a -> TBool
  Void a -> TVoid
  -- Like in c++, we both `func t : (x : @int) -> void` and `func s : (x : int) -> void` will have written type of
  -- (int) -> void so when getting type from written by user we cannot make any assumptions about passing args by reference
  FunT a tys ty -> TFun (map (\x -> (ByValue, getType x)) tys) (getType ty)
  Array a ins ty -> error "not implemented"

doTTypesMatch :: TType -> TType -> Bool
doTTypesMatch (TFun args1 returnType1) (TFun args2 returnType2) = (all (\(t1, t2) -> doTTypesMatch t1 t2) (zip (map snd args1) (map snd args2))) && (doTTypesMatch returnType1 returnType2)
doTTypesMatch t1 t2 = t1 == t2

runTypeChecker :: TypeCheckerMonad () -> Maybe TType -> TypeMap -> Either TypeCheckError ()
runTypeChecker tcm mtt tm = runIdentity $ evalStateT (runReaderT (runExceptT tcm) mtt) tm

typecheck :: Program -> Either TypeCheckError ()
typecheck prg = runTypeChecker (typeCheck prg) Nothing (M.empty)

