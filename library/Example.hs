{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | An example module.
module Example (main) where

import Prelude hiding (lookup)
import Data.Maybe
import Data.Map

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

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

type TcM m = ExceptT [String] (StateT Env (ReaderT Ctx m))

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

substInto :: Monad m => Var -> Exp -> Exp -> TcM m Exp
substInto v e = subst (singleton v e)

type Ctx = Map Var (Exp, Maybe Exp)

lookupType
  :: Monad m
  => Var -> TcM m Exp
lookupType x = do
  res <- asks (fmap fst . lookup x)
  case res of
    Just ty -> pure ty
    Nothing -> throwError ["The context contains no binding named " ++ show x]

lookupValue
  :: Monad m
  => Var -> TcM m (Maybe Exp)
lookupValue x = do
  res <- asks (fmap snd . lookup x)
  case res of
    Just val -> pure val
    Nothing -> throwError [show x ++ " has not been bound to any value."]

extendCtx :: Var -> Exp -> Maybe Exp -> Ctx -> Ctx
extendCtx x ty val = insert x (ty, val)

extendCtx' :: Var -> Exp -> Ctx -> Ctx
extendCtx' x ty = insert x (ty, Nothing)

inferType
  :: Monad m
  => Exp -> TcM m Exp
inferType =
  \case
    Variable x -> lookupType x
    Universe u -> pure $ Universe (u + 1)
    Pi (Abs x ty exp) -> do
      ty' <- inferUniverse ty
      exp' <- local (extendCtx' x ty) (inferUniverse exp)
      pure (Universe (max ty' exp'))
    Lambda (Abs x ty exp) -> do
      ty' <- inferUniverse ty
      exp' <- local (extendCtx' x ty) (inferType exp)
      pure (Pi (Abs x ty exp'))
    App f v -> do
      (Abs x s ty) <- inferPi f
      ty' <- inferType v
      checkEq s ty'
      substInto x ty' ty

inferUniverse :: Monad m => Exp -> TcM m Int
inferUniverse exp = do
  ty <- inferType exp
  norm <- normalize ty
  case norm of
    Universe k -> pure k
    _ -> throwError []

inferPi :: Monad m => Exp -> TcM m Abs
inferPi exp = do
  ty <- inferType exp
  norm <- normalize ty
  case norm of
    Pi k -> pure k
    _ -> throwError []

normalize :: Monad m => Exp -> TcM m Exp
normalize =
  \case
    v@(Variable x) -> do
      val <- lookupValue x
      case val of
        Nothing -> pure v
        Just exp -> normalize exp
    App f v -> do
      nv <- normalize v
      nf <- normalize f
      case nf of
        Lambda (Abs x _ f') -> do
          nf' <- substInto x v f'
          normalize nf'
        f' -> pure $ App f' nv
    u@(Universe _) -> pure u
    Pi a -> Pi <$> normalizeAbs a
    Lambda a -> Lambda <$> normalizeAbs a

normalizeAbs :: Monad m => Abs -> TcM m Abs
normalizeAbs (Abs x ty exp) = do
  ty' <- normalize ty
  exp' <- local (extendCtx x ty' Nothing) $ normalize exp
  pure (Abs x ty' exp')

checkEq :: Monad m => Exp -> Exp -> TcM m ()
checkEq s ty = do
  isEq <- equalInCtx s ty
  unless isEq $ throwError ["adf"]

equalInCtx :: Monad m => Exp -> Exp -> TcM m Bool
equalInCtx a b = do
  a' <- normalize a
  b' <- normalize b
  equalInCtx' a' b'

  where
    equalInCtx' (Variable v) (Variable v') = pure $ v == v'
    equalInCtx' (Universe k) (Universe k') = pure $ k == k'
    equalInCtx' (App f v) (App f' v') = pure $ (f == f') && (v == v')
    equalInCtx' (Pi p) (Pi p') = equalAbs p p'
    equalInCtx' (Lambda p) (Lambda p') = equalAbs p p'

    equalAbs (Abs x ty exp) (Abs x' ty' exp') = do
      exp'' <- substInto x' (Variable x) exp'
      pure $ (ty == ty') && (exp' == exp'')

initialEnv :: Env
initialEnv = Env {sym = 0}

initialCtx :: Ctx
initialCtx = empty

typecheck :: Monad m => TcM m a -> m (Either [String] a)
typecheck = flip runReaderT initialCtx . flip evalStateT initialEnv . runExceptT

demo :: IO (Either [String] ())
demo =
  typecheck $ do
    let v = Str "asdf"
    x <- fresh v
    liftIO $ print x
    x <- fresh v
    liftIO $ print x
