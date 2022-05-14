{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Interpreter where

import AbsFrappe
import PrintFrappe
import TypeChecker hiding (makeError, Position)

import Data.String
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

type Location = Int
type IdentToLocation = M.Map Ident Location
type LocationToValue = M.Map Location Value
type RunTimeError = String
type Position = BNFC'Position

data ValueOrLoc = Value' Value | Loc' Location

data Value 
  = VInt Integer 
  | VBool Bool 
  | VString String 
  | VFun [ArgWay] ([ValueOrLoc] -> InterpreterMonad Value)
  | VVoid 
  | VUninitializedFunction -- Value assigned to function variables declared but with no assignment.
  | VNotReturned -- Special pseudovalue used to check whether a function returned something.

instance Show Value where
  show v = case v of
    VInt num -> show num 
    VBool b -> show b
    VString str -> str 
    VFun _ _ -> "Function"
    VVoid -> "void"
    VUninitializedFunction -> "UninitializedFunction"
    VNotReturned -> "NotReturnedFromFunction"

-- Exception is used both as a way of throwing errors and for non-local jumps (return statement).
data Exception = RunTimeErrorExc RunTimeError | ReturnExc Value 
data EnvAndState = EnvAndState IdentToLocation LocationToValue

makeError :: Position -> String -> Exception
makeError pos errorString = RunTimeErrorExc ((case pos of
  Just (row, column) -> ("RunTimeError at row " ++ show row ++ ", column " ++ show column ++ ": ")
  Nothing -> "RunTimeError: ") ++ errorString ++ ".")

returnValue :: Value -> Exception
returnValue = ReturnExc

-- Propagates the error if it is not a return.
catchReturnValue :: Exception -> InterpreterMonad Value
catchReturnValue (ReturnExc value) = return value
catchReturnValue err = throwError err

valueFromId :: Ident -> EnvAndState -> Maybe Value
valueFromId id (EnvAndState env state) = do
  loc <- M.lookup id env
  value <- M.lookup loc state
  return value

-- "typechecker error" is used whenever a situation is impossible for interpreter, as typechecker 
-- should throw an error before
valueForId :: Ident -> Value -> EnvAndState -> EnvAndState
valueForId id value (EnvAndState env state) = EnvAndState env (M.insert (fromMaybe (error "typechecker error") (M.lookup id env)) value state)

getEnv :: EnvAndState -> IdentToLocation
getEnv (EnvAndState env _) = env

putEnv :: IdentToLocation -> EnvAndState -> EnvAndState
putEnv env (EnvAndState _ state) = (EnvAndState env state)

-- Locations are not being freed so they are assigned from 0 onwards.
newloc :: LocationToValue -> Location
newloc locToValue = M.size locToValue

matchIdentWithNewLocationAndSetValue :: Ident -> Value -> EnvAndState -> EnvAndState
matchIdentWithNewLocationAndSetValue id value (EnvAndState env state) = 
  let loc = newloc state in (EnvAndState (M.insert id loc env) (M.insert loc value state))

matchIdentWithLocation :: Ident -> Location -> EnvAndState -> EnvAndState
matchIdentWithLocation id loc (EnvAndState env state) = (EnvAndState (M.insert id loc env) state)

getLocationFromIdent :: Ident -> EnvAndState -> Location
getLocationFromIdent id (EnvAndState env _) = fromMaybe (error "typechecker error") (M.lookup id env)

getArgWayAndIdent :: Arg -> (ArgWay, Ident)
getArgWayAndIdent (Arg _ id _) = (ByValue, id)
getArgWayAndIdent (ArgRef _ id _) = (ByReference, id)

type InterpreterMonad = ExceptT Exception (StateT EnvAndState IO)

interpretProgram :: Program -> InterpreterMonad ()
interpretProgram (Program _ stmts) = forM_ stmts interpretStmt
---------------------------------------------------------------------------------

interpretStmt :: Stmt -> InterpreterMonad ()

interpretStmt (FnDef pos ident args _ (Block _ stmts)) = do
  currentEnv <- gets getEnv
  let argWays = map (fst . getArgTType) args
  let f valueOrLocs = do
      -- In function body, which will be run, environment from the place of declaration is being used.
      modify $ putEnv currentEnv
      modify $ matchIdentWithNewLocationAndSetValue ident (VFun argWays f)
      forM_ (zip args valueOrLocs) (\x -> case x of
        (Arg _ id _, Value' value) -> modify $ matchIdentWithNewLocationAndSetValue id value
        (ArgRef _ id _, Loc' loc) -> modify $ matchIdentWithLocation id loc
        _ -> error "typechecker error")
      -- If function does not reach a return statement foldM will run without an exception an will yield VNotReturned value.
      -- Otherwise return Exception is being thrown and catched and we get the returned value this way.
      returnedValue <- (foldM (\_ stmt -> interpretStmt stmt >> return VNotReturned) VNotReturned stmts) `catchError` catchReturnValue
      case returnedValue of
        VNotReturned -> throwError $ makeError pos "function does not reach return statement"
        rv -> return rv

  modify $ matchIdentWithNewLocationAndSetValue ident (VFun argWays f)

interpretStmt (Empty _) = return ()

interpretStmt (BStmt _ (Block _ stmts)) = do
  savedEnv <- gets getEnv
  forM_ stmts interpretStmt
  modify $ putEnv savedEnv

interpretStmt (Decl pos items t) = do
  -- Default values assigned at declaration: int = 0; string = ""; bool = false; function is undefined.
  defaultValue <- case (getType t) of
    TInt -> return $ VInt 0
    TString -> return $ VString ""
    TBool -> return $ VBool False
    TVoid -> error "typechecker error"
    TFun _ _ -> return $ VUninitializedFunction
  forM_ items (\item -> case item of
    NoInit _ id -> modify $ matchIdentWithNewLocationAndSetValue id defaultValue)
  return ()

interpretStmt (Ret _ expr) = do
  exprValue <- evalExpr expr
  throwError $ returnValue exprValue

interpretStmt (VRet _) = throwError $ returnValue VVoid

interpretStmt (Ass pos lsa expr) = do
  exprValue <- evalExpr expr
  case lsa of
    LSAIdent _ id -> modify $ valueForId id exprValue

interpretStmt (SExp _ expr) = do
  evalExpr expr
  return ()

interpretStmt (Incr pos id) = do
  maybeValue <- gets $ valueFromId id
  case maybeValue of
    Just (VInt num) -> do
      modify $ valueForId id (VInt (num + 1))
    Nothing -> error "typechecker error"

interpretStmt (Decr pos id) = do
  maybeValue <- gets $ valueFromId id
  case maybeValue of
    Just (VInt num) -> do
      modify $ valueForId id (VInt (num - 1))
    Nothing -> error "typechecker error"

interpretStmt (Cond _ expr block@(Block pos _)) = do
  exprValue <- evalExpr expr
  boolValue <- case exprValue of
    VBool b -> return b
    _ -> error "typechecker error"
  when boolValue (interpretStmt (BStmt pos block))

interpretStmt (CondElse _ expr block1@(Block pos1 _) block2@(Block pos2 _)) = do
  exprValue <- evalExpr expr
  boolValue <- case exprValue of
    VBool b -> return b
    _ -> error "typechecker error"
  if boolValue 
    then interpretStmt $ BStmt pos1 block1
    else interpretStmt $ BStmt pos2 block2

interpretStmt stmt@(While _ expr block@(Block pos _)) = do
  exprValue <- evalExpr expr
  boolValue <- case exprValue of
    VBool b -> return b
    _ -> error "typechecker error"
  when boolValue (do 
    interpretStmt (BStmt pos block)
    interpretStmt stmt)

interpretStmt (Print pos exprs) = do
  strs <- forM exprs (\expr -> do
    value <- evalExpr expr
    case value of
      VInt num -> return $ show num
      VBool b -> return $ show b
      VString str -> return str
      _ -> error "typechecker error")
  let concatenatedStrs = concat strs
  liftIO . putStrLn $ concatenatedStrs

-------------------------------------------------------------------------------

getMulOp :: MulOp -> Integer -> Integer -> Integer
getMulOp (Times _) = (*)
getMulOp (Div _) = div
getMulOp (Mod _) = mod

getAddOp :: AddOp -> Integer -> Integer -> Integer
getAddOp (Plus _) = (+)
getAddOp (Minus _) = (-)

getRelOp :: RelOp -> Integer -> Integer -> Bool
getRelOp relOp = case relOp of
  LTH _ -> (<)
  LE _ -> (<=)
  GTH _ -> (>)
  GE _ -> (>=)
  EQU _ -> (==)
  NE _ -> (/=)
---------------------------------------------------

evalExpr :: Expr -> InterpreterMonad Value
evalExpr expr = case expr of
  EVar pos id -> do
    maybeValue <- gets $ valueFromId id
    case maybeValue of
      Just t -> return t
      Nothing -> error "typechecker error"
  
  ELitInt pos num -> return $ VInt num
  
  ELitTrue pos -> return $ VBool True
  
  ELitFalse pos -> return $ VBool False
  
  EString pos str -> return $ VString str
  
  Neg pos expr -> do
    exprValue <- evalExpr expr
    intValue <- case exprValue of
      VInt num -> return num
      _ -> error "typechecker error"
    return $ VInt $ negate intValue
  
  Not pos expr -> do
    exprValue <- evalExpr expr
    boolValue <- case exprValue of
      VBool b -> return b
      _ -> error "typechecker error"
    return $ VBool $ not boolValue
  
  EMul pos expr1 mulOp expr2 -> do
    exprValue1 <- evalExpr expr1
    intValue1 <- case exprValue1 of
      VInt num -> return num
      _ -> error "typechecker error"
    exprValue2 <- evalExpr expr2
    intValue2 <- case exprValue2 of
      VInt num -> return num
      _ -> error "typechecker error"
    case mulOp of
      Times _ -> return ()
      -- 0 division problem is applicable to both division and modulo
      _ -> when (intValue2 == 0) (throwError $ makeError pos "division by 0")
    return $ VInt ((getMulOp mulOp) intValue1 intValue2)    
  
  EAdd pos expr1 addOp expr2 -> do
    exprValue1 <- evalExpr expr1
    intValue1 <- case exprValue1 of
      VInt num -> return num
      _ -> error "typechecker error"
    exprValue2 <- evalExpr expr2
    intValue2 <- case exprValue2 of
      VInt num -> return num
      _ -> error "typechecker error"
    return $ VInt ((getAddOp addOp) intValue1 intValue2) 
  
  ERel pos expr1 relOp expr2 -> do
    exprValue1 <- evalExpr expr1
    intValue1 <- case exprValue1 of
      VInt num -> return num
      _ -> error "typechecker error"
    exprValue2 <- evalExpr expr2
    intValue2 <- case exprValue2 of
      VInt num -> return num
      _ -> error "typechecker error"
    return $ VBool ((getRelOp relOp) intValue1 intValue2) 
  
  EAnd pos expr1 expr2 -> do
    exprValue1 <- evalExpr expr1
    boolValue1 <- case exprValue1 of
      VBool b -> return b
      _ -> error "typechecker error"
    exprValue2 <- evalExpr expr2
    boolValue2 <- case exprValue2 of
      VBool b -> return b
      _ -> error "typechecker error"
    return $ VBool (boolValue1 && boolValue2)
  
  EOr pos expr1 expr2 -> do
    exprValue1 <- evalExpr expr1
    boolValue1 <- case exprValue1 of
      VBool b -> return b
      _ -> error "typechecker error"
    exprValue2 <- evalExpr expr2
    boolValue2 <- case exprValue2 of
      VBool b -> return b
      _ -> error "typechecker error"
    return $ VBool (boolValue1 || boolValue2)
  
  EApp pos id exprs -> do
    maybeFunction <- gets $ valueFromId id
    case maybeFunction of
      -- func is of type [ValueOrLoc] -> InterpreterMonad Value
      Just (VFun argWays func) -> do
        -- We check what way were the arguments passed. If by value we need just value, if by reference, we need the location.
        valOrLocs <- forM (zip argWays exprs) (\x -> case x of
          (ByReference, (EVar _ id)) -> fmap Loc' (gets $ getLocationFromIdent id)
          (ByValue, expr) -> fmap Value' (evalExpr expr)
          _ -> error "typechecker error")
        savedEnv <- gets getEnv
        returnValue <- func valOrLocs
        modify $ putEnv savedEnv
        return returnValue
      _ -> error "typechecker error"

  ELambda pos args returnType (Block _ stmts) -> do
    currentEnv <- gets getEnv
    let argWays = map (fst . getArgTType) args
    let f valueOrLocs = do
        -- In function body, which will be run, environment from the place of declaration is being used.
        modify $ putEnv currentEnv
        forM_ (zip args valueOrLocs) (\x -> case x of
          (Arg _ id _, Value' value) -> modify $ matchIdentWithNewLocationAndSetValue id value
          (ArgRef _ id _, Loc' loc) -> modify $ matchIdentWithLocation id loc
          _ -> error "typechecker")
        returnedValue <- (foldM (\_ stmt -> interpretStmt stmt >> return VNotReturned) VNotReturned stmts) `catchError` catchReturnValue
        case returnedValue of
          VNotReturned -> throwError $ makeError pos "function does not reach return statement"
          rv -> return rv
    return (VFun argWays f)

--------------------------------------------------------------------------------

interpret :: Program -> IO ()
interpret prg = do
  result <- evalStateT (runExceptT $ interpretProgram prg) (EnvAndState M.empty M.empty)
  case result of
    Left err -> case err of
      RunTimeErrorExc err -> putStrLn err
      ReturnExc _ -> error "typechecker error"
    Right _ -> return ()

------------------------------------------------------
