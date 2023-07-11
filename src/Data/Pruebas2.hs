-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Pruebas2
  ( PRF (..),
    Natural,
    -- Flip,
    Void,
    KnownPRFExtension,
    Constructors (..),
    KnownPRFExtensions,
    AllConstructors,
  )
where

import Data.Finite (Finite)
import Data.Kind (Constraint, Type)
-- import Data.Proxy (Proxy (..))
-- import Data.Type.Map
import Data.Void (Void)
import GHC.Natural (Natural)
import GHC.TypeLits (Symbol)
import GHC.TypeNats

type family Every (xs :: [k]) (c :: k -> Constraint) :: Constraint where
  Every '[] _ = ()
  Every (x ': xs) c = (c x, Every xs c)

-- type family Map (f :: k1 -> k2) (xs :: [k1]) :: [k2] where
--   Map f '[] = '[]
--   Map f (x ': xs) = f x ': Map f xs

-- type family Map1 (f :: k1 -> k2 -> k3) (xs :: [k1]) (par :: k2) :: [k3] where
--   Map1 f '[] _ = '[]
--   Map1 f (x ': xs) par = f x par ': Map1 f xs par

-- type family Flip (f :: k1 -> k2 -> k3) (x :: k2) (y :: k1) :: k3 where
--   Flip f x y = f y x

type family GetCons (k :: Symbol) (ks :: [Symbol]) :: Nat -> Type where
  GetCons k (k ': ks) = Constructors k
  GetCons k (_ ': ks) = GetCons k ks

type family Has (k :: k1) (ks :: [k1]) :: Bool where
  Has k '[] = 'False
  Has k (k ': ks) = 'True
  Has k (_ : ks) = Has k ks

-- foo :: forall ks. Proxy (Has "Hello" ks) -> GetCons "Hello" ks 7
-- foo Proxy = Foo

data PRF :: [Symbol] -> Nat -> Type where
  Z :: PRF exts 0
  S :: PRF exts 1
  U :: (KnownNat n) => Finite n -> PRF exts n
  Extra ::
    (KnownNat n, KnownPRFExtensions exts) =>
    AllConstructors exts n ->
    PRF exts n

class KnownPRFExtension (ext :: Symbol) where
  data Constructors ext (n :: Nat)

class KnownPRFExtensions exts where
  type AllConstructors exts (n :: Nat)

instance KnownPRFExtension "Hello" where
  data Constructors "Hello" n = Foo

{-

instance Every exts KnownPRFExtension => KnownPRFExtensions exts where
  type AllConstructors exts n = Map1 Constructors exts n

data OneOf (xs :: [k]) where
  Here :: x -> OneOf (x ': xs)
  There :: OneOf xs -> OneOf (y ': xs)

instance Every xs Show => Show (OneOf xs) where
  show (Here x) = "Here " <> show x
  show (There x) = "There (" <> show x <> ")"

-}
