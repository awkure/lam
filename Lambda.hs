{-# LANGUAGE TypeFamilies #-}

module Lambda where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Function         (on)
import           Data.Functor.Foldable
import qualified Data.Map              as Map

type Name = String

data Expr
    = Var Name
    | Lit Ground
    | App Expr Expr
    | Lam Name Type Expr

data Ground
    = LInt Int
    | LBool Bool

data Type
    = TInt
    | TBool
    | TArr Type Type
    deriving Eq

type Entry = (Name, Type)
type Env = [Entry]

data TypeError
    = Mismatch Type Type
    | NotFunction Type
    | NotInScope Name

type Infer = ExceptT TypeError (Reader Env)

extend :: Entry -> Env -> Env
extend = (:)

inEnv :: Entry -> Infer a -> Infer a
inEnv = local . extend

lookupVar :: Name -> Infer Type
lookupVar x = do
  env <- ask
  case lookup x env of
    Just e  -> return e
    Nothing -> throwError $ NotInScope x

infer :: Expr -> Infer Type
infer (Lit LInt  {}) = return TInt
infer (Lit LBool {}) = return TBool
infer (Var x) = lookupVar x
infer (Lam x t e) = do
    rhs <- (x,t) `inEnv` (infer e)
    return (TArr t rhs)
infer (App e1 e2) = do
    t1 <- infer e1
    t2 <- infer e2
    case t1 of
       (TArr a b) | a == t2 -> return b
                  | otherwise -> throwError $ Mismatch t2 a
       ty -> throwError $ NotFunction ty

runInfer :: Env -> Infer a -> Either TypeError a
runInfer env = flip runReader env . runExceptT

inferTop :: Env -> Expr -> Either TypeError Type
inferTop = (. infer) . runInfer

data Value
  = VInt Integer
  | VBool Bool
  | VClosure String Expr Scope

instance Show Value where
  show (VInt  x)  = show x
  show (VBool x)  = show x
  show VClosure{} = "#closure"

type Scope = Map.Map String Value

eval :: Scope -> Expr -> Value
eval env (Lit (LInt  x)) = VInt $ fromIntegral x
eval env (Lit (LBool x)) = VBool x
eval env (Var x)         = env Map.! x
eval env (Lam x _ body)  = VClosure x body env
eval env (App a b)       = (lapp `on` eval env) a b

lapp :: Value -> Value -> Value
lapp (VClosure v t e) t' = eval (Map.insert v t' e) t
lapp _                _  = error "Error applying closure"

_true  = Lam "a0" TBool $ Lam "a1" TBool $ Var "a1"
_false = Lam "a0" TBool $ Lam "a1" TBool $ Var "a0"
_and   = Lam "a0" TBool $ Lam "a1" TBool $ App (App (Var "a1") (Var "a0")) _false
_or    = Lam "a0" TBool $ Lam "a1" TBool $ App (App (Var "a1") _true) (Var "a0")
_not   = Lam "a0" TBool $ App (App (Var "a0") _false) _true

-- exec t []     = t
-- exec t (x:xs) = exec (lapp t x) xs
exec t = cata phi where
    phi Nil        = t
    phi (Cons a b) = lapp (lapp t a) b

main :: IO ()
main = do
    let t = App _not (App (App _or _true) (App (App _and _true) _false))
    let res = exec (eval Map.empty t) [VBool True, VBool False]
    putStrLn $ show res -- false
