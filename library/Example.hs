{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | An example module.
module Example (main) where

import Prelude hiding (lookup)
import Data.Maybe
import Data.Map

import Control.Monad.State
import Control.Monad.Except

-- | An example function.
main :: IO ()
main = return ()

data Var
  = Str String
  | Gensym String
           Int
  | Dummy
  deriving (Show, Eq, Ord)

data Abs = Abs
  { var :: Var
  , ty :: Exp
  , expr :: Exp
  } deriving (Show, Eq)

data Exp
  = Variable Var
  | Universe Int
  | Pi Abs
  | Lambda Abs
  | App Exp
        Exp
  deriving (Show, Eq)

data Env = Env { sym :: Int }

type TcM m = ExceptT [String] (StateT Env m)

fresh :: Monad m => Var -> TcM m Var
fresh Dummy = pure Dummy
fresh (Gensym x _) = fresh (Str x)
fresh (Str x) = do
  ctr <- gets sym
  modify (\e -> e { sym = ctr + 1})
  pure (Gensym x ctr)

subst' :: Monad m => Map Var Exp -> Abs -> TcM m Abs
subst' ctx (Abs x ty env) = do
  x' <- fresh x
  ty' <- subst ctx ty
  env' <- subst (insert x (Variable x') ctx) env
  pure $ Abs x' ty' env'

subst :: Monad m => Map Var Exp -> Exp -> TcM m Exp
subst ctx =
  \case
    Pi abs -> Pi <$> subst' ctx abs
    Lambda abs -> Lambda <$> subst' ctx abs
    App f v -> App <$> subst ctx f <*> subst ctx v
    v@(Variable x) -> pure $ findWithDefault v x ctx
    u@(Universe _) -> pure u

type Ctx = Map Var (Exp, Maybe Exp)

lookupType
  :: Monad m
  => Var -> Ctx -> TcM m Exp
lookupType x ctx = do
  let res = fst <$> lookup x ctx
  case res of
    Just ty -> pure ty
    Nothing -> throwError ["The context contains no binding named " ++ show x]

lookupValue
  :: Monad m
  => Var -> Ctx -> TcM m (Maybe Exp)
lookupValue x ctx = do
  let res = snd <$> lookup x ctx
  case res of
    Just val -> pure val
    Nothing -> throwError [show x ++ " has not been bound to any value."]

extendCtx :: Var -> Exp -> Maybe Exp -> Ctx -> Ctx
extendCtx x ty val = insert x (ty, val)

inferType ctx =
  \case
    Variable x -> lookupType x ctx
    Universe u -> pure $ Universe (u + 1)
    Pi (Abs x ty exp) -> do
      kty <- inferUniverse ctx ty
      kexp <- inferUniverse (extendCtx x ty Nothing ctx) exp
      pure (Universe (max kty kexp))
    Lambda abs@(Abs x ty exp) -> do
      ty' <- inferUniverse ctx ty
      exp' <- inferType (extendCtx x ty Nothing ctx) exp
      pure (Pi (abs {expr = exp'}))
    App f v -> do
      (Abs x s ty) <- inferPi ctx f
      ty' <- inferType ctx v
      checkEq ctx s ty'
      subst (singleton x ty') ty

inferUniverse :: Monad m => Ctx -> Exp -> TcM m Int
inferUniverse ctx exp = do
  ty <- inferType ctx exp
  norm <- normalize ctx ty
  case norm of
    Universe k -> pure k
    _ -> throwError []

inferPi :: Monad m => Ctx -> Exp -> TcM m Abs
inferPi ctx exp = do
  ty <- inferType ctx exp
  norm <- normalize ctx ty
  case norm of
    Pi k -> pure k
    _ -> throwError []

normalize :: Monad m => Ctx -> Exp -> TcM m Exp
normalize ctx =
  \case
    v@(Variable x) -> do
      val <- lookupValue x ctx
      case val of
        Nothing -> pure v
        Just exp -> normalize ctx exp
    App f v -> do
      nv <- normalize ctx v
      nf <- normalize ctx f
      case nf of
        Lambda (Abs x _ f') -> do
          nf' <- subst (singleton x v) f'
          normalize ctx nf'
        f' -> pure $ App f' nv
    u@(Universe _) -> pure u
    Pi a -> Pi <$> normalizeAbs ctx a
    Lambda a -> Lambda <$> normalizeAbs ctx a

normalizeAbs :: Monad m => Ctx -> Abs -> TcM m Abs
normalizeAbs ctx (Abs x ty exp) = do
  ty' <- normalize ctx ty
  exp' <- normalize (extendCtx x ty' Nothing ctx) exp
  pure (Abs x ty' exp')

checkEq :: Monad m => Ctx -> Exp -> Exp -> TcM m ()
checkEq ctx s ty = do
  isEq <- equalInCtx ctx s ty
  unless isEq $ throwError ["adf"]

equalInCtx :: Monad m => Ctx -> Exp -> Exp -> TcM m Bool
equalInCtx ctx a b = do
  a' <- normalize ctx a
  b' <- normalize ctx b
  equalInCtx' a' b'

  where
    equalInCtx' (Variable v) (Variable v') = pure $ v == v'
    equalInCtx' (Universe k) (Universe k') = pure $ k == k'
    equalInCtx' (App f v) (App f' v') = pure $ (f == f') && (v == v')
    equalInCtx' (Pi p) (Pi p') = equalAbs p p'
    equalInCtx' (Lambda p) (Lambda p') = equalAbs p p'

    equalAbs (Abs x ty exp) (Abs x' ty' exp') = do
      exp'' <- subst (singleton x' (Variable x)) exp'
      pure $ (ty == ty') && (exp' == exp'')

initialEnv :: Env
initialEnv = Env {sym = 0}

typecheck :: Monad m => TcM m a -> m (Either [String] a)
typecheck = flip evalStateT initialEnv . runExceptT

demo :: IO (Either [String] ())
demo =
  typecheck $ do
    let v = Str "asdf"
    x <- fresh v
    liftIO $ print x
    x <- fresh v
    liftIO $ print x
