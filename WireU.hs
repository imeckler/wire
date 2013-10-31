{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable #-}
module WireU where

import Prelude hiding (foldr)
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Error
import Control.Applicative
import Data.Traversable
import Data.Foldable

data Wire a
  = PlusU a
  | PlusC a
  | PlusA a
  | MultU a
  | MultC a
  | MultA a
  | MultZ a
  | Distrib a
  | Par (Wire a) (Wire a) a
  | Choice (Wire a) (Wire a) a
  | Comp (Wire a) (Wire a) a
  | Flip (Wire a) a
  | Fix (Wire a) a
  | Id a
  | RecNat a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data MonoTy = Zero | One | Nat deriving (Eq, Ord, Show)

data Ty
  = Mono MonoTy
  | Poly Int
  | Ty :+ Ty
  | Ty :* Ty
  deriving (Eq, Ord, Show)

type CheckT m a = StateT Int (ErrorT String m) a

fresh :: Monad m => StateT Int m Int
fresh = do
  x <- get
  put (x + 1)
  return x

pairWith :: (a -> b -> c) -> (a, a) -> (b, b) -> (c, c)
pairWith f (x, y) (a, b) = (f x a, f y b)

meet :: (Applicative m, Monad m) => Ty -> Ty -> CheckT m [(Int, Ty)]
meet (Mono t) (Mono s)
  | t == s    = pure []
  | otherwise = throwError "Mono error"
meet (Poly t) (Mono s) = pure [(t, Mono s)]
meet t        (Poly s) = pure [(s, t)]
meet (Poly t) s        = pure [(t, s)]
meet (t :+ s) (a :+ b) = (++) <$> meet t a <*> meet s b
meet (t :* s) (a :* b) = (++) <$> meet t a <*> meet s b
meet _        _        = throwError "meet error"

conjA :: Applicative m => (m a, m b) -> m (a, b)
conjA (x, y) = (,) <$> x <*> y

constrain :: Ty -> [(Int, Ty)] -> Ty
constrain (Poly n) cs = maybe (Poly n) id $ lookup n cs
constrain (Mono t) _  = Mono t
constrain (x :+ y) cs = constrain x cs :+ constrain y cs
constrain (x :* y) cs = constrain x cs :* constrain y cs

cType :: (Monad m, Functor m) => ((t, t) -> b) -> (Ty -> Ty -> t) -> StateT Int m b
cType f c = do
  [x, y] <- replicateM 2 (Poly <$> fresh)
  pure (f (c x y, c y x))

aType :: (Monad m, Functor m) => ((Ty, Ty) -> b) -> (Ty -> Ty -> Ty) -> StateT Int m b
aType f c = do
  [x, y, z] <- replicateM 3 (Poly <$> fresh)
  pure (f (c x (c y z), c (c x y) z))

wireVal :: Wire a -> a
wireVal (Id x)         = x
wireVal (PlusU x)      = x
wireVal (PlusC x)      = x
wireVal (PlusA x)      = x
wireVal (MultU x)      = x
wireVal (MultC x)      = x
wireVal (MultA x)      = x
wireVal (MultZ x)      = x
wireVal (Distrib x)    = x
wireVal (Par _ _ x)    = x
wireVal (Choice _ _ x) = x
wireVal (Comp _ _ x)   = x
wireVal (Flip _ x)     = x
wireVal (RecNat x)     = x

typeOf :: (Monad m, Applicative m) => Wire () -> CheckT m (Wire (Ty, Ty))
-- typeOf (Comp w1 w2) = join . fmap conjA $ pairWith meet <$> typeOf w1 <*> typeOf w2

typeOf (Id _) = (\x -> Id (x, x)) . Poly <$> fresh

typeOf (PlusU _) = (\x -> PlusU (Mono Zero :+ x, x)) . Poly <$> fresh

typeOf (PlusC _) = cType PlusC (:+)

typeOf (PlusA _) = aType PlusA (:+)

typeOf (MultU _) = (\x -> MultU (Mono One :* x, x)) . Poly <$> fresh

typeOf (MultC _) = cType MultC (:*)

typeOf (MultA _) = aType MultA (:*)

typeOf (MultZ _) = (\x -> MultZ (Mono Zero :* x, x)) . Poly <$> fresh

typeOf (Distrib _) = do
  [x, y, z] <- replicateM 3 (Poly <$> fresh)
  pure $ Distrib ((x :+ y) :* z, (x :* z) :+ (y :* z))

typeOf (Par w1 w2 _) = do
  w1' <- typeOf w1
  w2' <- typeOf w2
  pure $ Par w1' w2' (pairWith (:*) (wireVal w1') (wireVal w2'))

typeOf (Choice w1 w2 _) = do
  w1' <- typeOf w1
  w2' <- typeOf w2
  pure $ Par w1' w2' (pairWith (:+) (wireVal w1') (wireVal w2'))


typeOf (Comp w1 w2 _) = do
  w1' <- typeOf w1
  w2' <- typeOf w2

  let (a1, b1) = wireVal w1'
      (a2, b2) = wireVal w2'

  cs  <- meet b1 a2
  pure . fmap (both (`constrain` cs)) $ Comp w1' w2' (a1, b2)

typeOf (Flip w _) = (\w' -> Flip w' (swap $ wireVal w')) <$> typeOf w

typeOf (RecNat _) = pure $ RecNat (Mono Nat, Mono One :+ Mono Nat)

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

runCheckT :: Monad m => CheckT m a -> m (Either String a)
runCheckT mx = runErrorT (evalStateT mx 0)

annotate :: Wire () -> Maybe (Wire (Ty, Ty))
annotate = either (const Nothing) Just . runIdentity . runCheckT . typeOf

monomorphicTy :: Ty -> Bool
monomorphicTy (Poly _) = False
monomorphicTy (Mono _) = True
monomorphicTy (a :+ b) = monomorphicTy a && monomorphicTy b
monomorphicTy (a :* b) = monomorphicTy a && monomorphicTy b

monomorphic :: Wire (Ty, Ty) -> Bool
monomorphic = foldr (\(x, y) r -> monomorphicTy x && monomorphicTy y && r) True

