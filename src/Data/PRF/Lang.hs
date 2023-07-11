{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Data.PRF.Lang
  ( -- | Utilidades variadas para extender el lenguaje

    -- * Tipo suma y punto fijo de orden superior
    HSum (..),
    HFix (..),

    -- * Functores y monadas con parametro
    HFunctor (..),
    HMonad (..),

    -- * Extension vacia de un lenguaje
    EmptyExt,

    -- * Funciones utiles
    heither,
    -- heither',

    -- * Clase inyeccion
    Inclusion (..),
    UseL (..),
    UseR (..),
  )
where

import Data.Kind (Constraint, Type)

data HSum a b par = L (a par) | R (b par)
  deriving (Eq, Ord, Show, Read)

newtype HFix f par = F (f (HFix f) par)

data EmptyExt par deriving (Eq, Ord, Show, Read)

-- Para hacerlo mas legible usare sinonimos
class HFunctor lang where
  -- Analogo al Functor que depende de un parametro en un dominio
  -- restringido
  type Par lang (par :: k) :: Constraint
  hmap ::
    forall ext1 ext2 par'.
    Par lang par' =>
    ( forall par.
      Par lang par =>
      ext1 par ->
      ext2 par
    ) ->
    lang ext1 par' ->
    lang ext2 par'

class HFunctor lang => HMonad (lang :: (k -> Type) -> (k -> Type)) where
  -- Analogo a la monada que depende de un parametro en un dominio
  -- restringido.
  -- hmap f == hbind (hreturn . f)

  hreturn ::
    forall ext par.
    Par lang par =>
    ext par ->
    lang ext par

  hbind ::
    forall ext1 ext2 par'.
    Par lang par' =>
    ( forall par.
      Par lang par =>
      ext1 par ->
      lang ext2 par
    ) ->
    lang ext1 par' ->
    lang ext2 par'

  infixl 2 >>>=
  (>>>=) ::
    forall ext1 ext2 par'.
    Par lang par' =>
    lang ext1 par' ->
    ( forall par.
      Par lang par =>
      ext1 par ->
      lang ext2 par
    ) ->
    lang
      ext2
      par'
  hx >>>= f = hbind f hx

instance HFunctor (HSum a) where
  type Par (HSum a) _ = ()
  hmap f = hbind (hreturn . f)

instance HMonad (HSum a) where
  hreturn = R
  hbind f = \case
    L x -> L x
    R y -> f y

-- Version parametrica de la funcion `either'
heither :: forall a b c par. (a par -> c) -> (b par -> c) -> HSum a b par -> c
heither f g = \case L x -> f x; R y -> g y

-- -- Version de `heither' que toma funciones polimorficas
-- heither' ::
-- forall a b c par'.
-- (forall par. a par -> c) ->
-- (forall par. b par -> c) ->
-- HSum a b par' ->
-- c
-- heither' f g = heither f g

instance (forall ext. Show (ext par) => Show (lang ext par)) => Show (HFix lang par) where
  show (F x) = "F(" ++ show x ++ ")"

instance (forall ext. Eq (ext par) => Eq (lang ext par)) => Eq (HFix lang par) where
  F x == F y = x == y

class Inclusion ext1 ext2 where
  inj :: ext1 par -> ext2 par

instance Inclusion ext ext where
  inj = id

newtype UseL ext par = UseL (ext par)

newtype UseR ext par = UseR (ext par)

-- Esto no sirve para mucho
instance Inclusion ext1 ext2 => Inclusion (UseL ext1) (HSum ext2 ext3) where
  inj (UseL x) = L (inj x)

instance Inclusion ext1 ext3 => Inclusion (UseR ext1) (HSum ext2 ext3) where
  inj (UseR x) = R (inj x)
