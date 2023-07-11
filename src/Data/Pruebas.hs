-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
-- {-# LANGUAGE EmptyCase #-}
-- {-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
-- {-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

--{-# LANGUAGE PolyKinds #-}
--{-# LANGUAGE UndecidableInstances #-}

module Pruebas
  ( PRF (..),
    Constructors (..),
    AllConstructors,
    KnownPRFExtension,
    KnownPRFExtensions,
    PRFBasica,
    PRFRapida,
    evalPRFBasica,
    pattern Rap,
    Delete,
    IsMember,
  )
where

import Data.Finite (Finite)
import Data.Kind (Type)
-- import Data.Proxy (Proxy (..))
-- import qualified Data.RBR as Rec
-- import Data.Singletons
import Data.Void (Void)
import GHC.Natural (Natural)
import GHC.TypeLits (Symbol)
import GHC.TypeNats

-- import GHC.Types --(Symbol ())

data PRF :: [Symbol] -> Nat -> Type where
  Z :: PRF exts 0
  S :: (KnownNat n) => PRF exts n
  U :: (KnownNat n) => Finite n -> PRF exts n
  Extra :: (KnownNat n, KnownPRFExtensions exts) => !(AllConstructors exts n) -> PRF exts n

type PRFBasica = PRF '[]

evalPRFBasica :: PRFBasica n -> [Natural] -> Natural
evalPRFBasica f v = case f of
  Z -> 0
  S -> head v + 1
  U n -> v !! (fromIntegral n)

class KnownPRFExtension (ext :: Symbol) where
  data Constructors ext :: Nat -> Type

class KnownPRFExtensions (exts :: [Symbol]) where
  type AllConstructors exts (n :: Nat) :: Type

instance KnownPRFExtensions '[] where
  type AllConstructors '[] n = Void -- Vacia

-- (KnownPRFExtension x, KnownPRFExtensions xs) => -- Por que es redundante?
instance KnownPRFExtensions (x ': xs) where
  type AllConstructors (x ': xs) n = Either (Constructors x n) (AllConstructors xs n)

instance KnownPRFExtension "FuncionesRapidas" where
  data Constructors "FuncionesRapidas" n where
    Mas :: Constructors "FuncionesRapidas" 2
    Menos :: Constructors "FuncionesRapidas" 2

pattern Rap :: (KnownNat n) => () => Constructors "FuncionesRapidas" n -> PRFRapida n
pattern Rap x = Extra (Left x)

{-# COMPLETE Z, S, U, Rap #-}

type PRFRapida = PRF '["FuncionesRapidas"]

type family Member (x :: k) (xs :: [k]) :: Bool where
  Member x '[] = 'False
  Member x (x ': xs) = 'True
  Member x (y ': xs) = Member x xs

type IsMember x xs = Member x xs ~ 'True

type family Add (x :: k) (xs :: [k]) :: [k] where
  Add x '[] = '[x]
  Add x (x ': xs) = x ': xs
  Add x (_ ': xs) = Add x xs

type family Delete (x :: k) (xs :: [k]) :: [k] where
  Delete x '[] = '[]
  Delete x (x ': xs) = xs
  Delete x (_ ': xs) = xs
