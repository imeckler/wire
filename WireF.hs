{-# LANGUAGE GADTs,
             DataKinds,
             RankNTypes,
             TypeOperators, 
             KindSignatures, 
             TypeFamilies, 
             TupleSections, 
             Arrows, 
             RebindableSyntax, 
             StandaloneDeriving, 
             FlexibleContexts, 
             UndecidableInstances,
             TypeSynonymInstances,
             FlexibleInstances #-}

module WireF where

import Data.Void
import Prelude hiding (pred, succ)
import Common
-- import Control.Monad.Cont

infixr 2 +++
infixr 1 >>>

type C a = forall r. ((a -> r) -> r)

inC :: a -> C a
inC x = \k -> k x

outC :: C a -> a
outC f = f id

type family Interp (a :: BallTy) :: *

data Mu f = Roll (f (Mu f))

deriving instance Show (f (Mu f)) => Show (Mu f)

deriving instance Eq (f (Mu f)) => Eq (Mu f)

-- type FComp f g a = f (g a)

-- type List a = Mu (FComp (Either ()) ((,) a))
type Nat = Mu (Either ())

instance Num Nat where
  fromInteger 0 = Roll (Left ())
  fromInteger n
    | n < 0     = error "Negative nat"
    | otherwise = Roll (Right (fromInteger (n - 1)))

  Roll (Left ()) + m = m
  Roll (Right n) + m = Roll (Right (n + m))

  Roll (Left ()) * _ = 0
  Roll (Right n) * m = m + n * m

  signum (Roll (Left ())) = 0
  signum _                = 1

  abs n = n

natToNum :: Num a => Nat -> a
natToNum (Roll (Left ())) = 0
natToNum (Roll (Right n)) = 1 + natToNum n

type instance Interp Zero = Void
type instance Interp One  = ()
type instance Interp NatB = Nat
type instance Interp (a :+ b) = Either (Interp a) (Interp b)
type instance Interp (a :* b) = (Interp a, Interp b)

data Ball :: BallTy -> * where
  BZero :: Ball Zero
  BOne  :: Ball One
  BProd :: Ball a -> Ball b -> Ball (a :* b)
  BL :: Ball a -> Ball (a :+ b)
  BR :: Ball b -> Ball (a :+ b)

data Wire :: BallTy -> BallTy -> * where
  PlusU   :: Wire (Zero :+ a) a
  PlusC   :: Wire (a :+ b) (b :+ a)
  PlusA   :: Wire (a :+ (b :+ c)) ((a :+ b) :+ c)
  MultU   :: Wire (One :* a) a
  MultC   :: Wire (a :* b) (b :* a)
  MultA   :: Wire (a :* (b :* c)) ((a :* b) :* c)
  MultZ   :: Wire (Zero :* b) Zero
  Distrib :: Wire ((a :+ b) :* c) ((a :* c) :+ (b :* c))

  Par    :: Wire a b -> Wire c d -> Wire (a :* c) (b :* d)
  Choice :: Wire a b -> Wire c d -> Wire (a :+ c) (b :+ d)
  Comp   :: Wire a b -> Wire b c -> Wire a c
  Flip   :: Wire a b -> Wire b a
  Fix    :: Wire (a :+ b) (a :+ c) -> Wire b c
  Id     :: Wire a a

  RecNat :: Wire NatB (One :+ NatB)

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

nothing :: Wire (Zero :+ a) a
nothing = PlusU

addNothing :: Wire a (Zero :+ a)
addNothing = Flip nothing

unroll :: Wire NatB (One :+ NatB)
unroll = RecNat

sym :: Wire a b -> Wire b a
sym = Flip

roll :: Wire (One :+ NatB) NatB
roll = Flip unroll

spin :: Wire Zero One
spin = Fix (PlusC >>> nothing >>> unroll >>> PlusC)

pred :: Wire NatB NatB
pred = unroll >>> (sym spin +++ Id) >>> nothing

succ :: Wire 'NatB 'NatB
succ = sym pred

-- add :: Wire (NatB :* NatB) (NatB :* One)

-- (loop : Nat, Nat) + (Nat, Nat) = (loop : Nat, Nat) + Nat
shift :: Wire ('NatB ':* 'NatB) (('One ':* 'NatB) ':+ ('NatB ':* 'NatB))
shift =   unroll *** Id
      >>> distrib
      >>> Id +++ (Id *** succ)

til :: (Either a b -> Either a c) -> (b -> c)
til f = go . f . Right
  where go = either (go . f . Left) id

lit :: (c -> b) -> (Either a c -> Either a b)
lit f = either Left (Right . f)

cnot :: Wire ((One :+ One) :* (One :+ One)) ((One :+ One) :* (One :+ One))
cnot = distrib
       >>> (unite >>> Id) +++ (unite >>> PlusC)
       >>> unit           +++ unit
       >>> factor

test :: Wire (One :+ (One :+ One)) (One :+ (One :+ One))
test = Id +++ Id

unite :: Wire (One :* a) a
unite = MultU

unit :: Wire a (One :* a)
unit = Flip unite

distrib :: Wire ((a ':+ b) ':* c) ((a ':* c) ':+ (b ':* c))
distrib = Distrib

factor :: Wire ((a :* c) :+ (b :* c)) ((a :+ b) :* c)
factor = Flip distrib

interpret :: Wire a b -> ((Interp a -> Interp b), (Interp b -> Interp a))
interpret PlusU = (either absurd id, Right)
interpret PlusC = (either Right Left, either Right Left)
interpret PlusA = ( either (Left . Left) (either (Left . Right) Right)
                  , either (either Left (Right . Left)) (Right . Right))
interpret MultU = (snd, \x -> ((), x))
interpret MultC = (swap, swap)
interpret MultA = ((\(x, (y, z)) -> ((x, y), z)), (\((x, y), z) -> (x, (y, z))))
interpret MultZ = (absurd . fst, absurd)
interpret Distrib = ( \(p, c) -> either (Left . (,c)) (Right . (,c)) p
                    , either (\(a, c) -> (Left a, c)) (\(b, c) -> (Right b, c)) )
interpret (Flip w) = swap (interpret w)

interpret (Fix w)  = (til f, til g) where (f, g) = interpret w

interpret Id = (id, id)
interpret (Comp w q) = (qf . wf, wg . qg) where
  (wf, wg) = interpret w
  (qf, qg) = interpret q

interpret (Par w q) = ((\(x, y) -> (wf x, qf y)), (\(a, b) -> (wg a, qg b))) where
  (wf, wg) = interpret w
  (qf, qg) = interpret q

interpret (Choice w q) = (either (Left . wf) (Right . qf), either (Left . wg) (Right . qg)) where
  (wf, wg) = interpret w
  (qf, qg) = interpret q

interpret RecNat = ((\(Roll x) -> x), Roll)

first :: Wire a b -> Wire (a :* c) (b :* c)
first w = Par w Id

second :: Wire a b -> Wire (c :* a) (c :* b)
second = Par Id

(***) :: Wire a b -> Wire a' b' -> Wire (a :* a') (b :* b')
(***) = Par

(+++) :: Wire a b -> Wire c d -> Wire (a :+ c) (b :+ d)
(+++) = Choice

-- A lie
(&&&) :: Wire a b -> Wire a c -> Wire a (b :* c)
(&&&) = undefined

(>>>) :: Wire a b -> Wire b c -> Wire a c
(>>>) = Comp

