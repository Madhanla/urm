{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Data.PRF.Antiguas.Pruebas
  ( -- Pruebas interesantes
    Nomad (..),
  )
where

import Data.Kind (Constraint)
import Data.PRF.Antiguas.PRFExt
import qualified Data.PRF.Antiguas.Utils as U

class Nomad (lang :: (k -> Type) -> (k -> Type)) where
  -- ejemplo
  type Par lang (par :: k) :: Constraint
  embed ::
    forall ext par.
    Par lang par =>
    ext par ->
    lang ext par

  bindFN ::
    forall ext1 ext2 par'.
    Par lang par' =>
    ( forall par.
      Par lang par =>
      ext1 par ->
      lang ext2 par
    ) ->
    lang ext1 par' ->
    lang ext2 par'

  nomap ::
    forall ext1 ext2 par'.
    Par lang par' =>
    ( forall par.
      Par lang par =>
      ext1 par ->
      ext2 par
    ) ->
    lang ext1 par' ->
    lang ext2 par'
  nomap f = bindFN (embed . f)

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
  f >>>= nx = bindFN nx f

-- (>>>=) = flip bindFN -- eso no funciona sin ImpredicativeTypes

--   liftN2 ::
--     forall ext1 ext2 ext3 par'.
--     Par lang par' =>
--     ( forall par.
--       Par lang par =>
--       ext1 par ->
--       ext2 par ->
--       ext3 par
--     ) ->
--     lang ext1 par' ->
--     lang ext2 par' ->
--     lang ext3 par'
-- liftN2 f nx ny = nx >>>= (\x -> ny >>>= (\y -> embed (f x y)))

--   (<***>) ::
--     forall ext1 ext2 par'.
--     Par lang par' =>
--     lang (Fun lang ext1 ext2) par' ->
--     lang ext1 par' ->
--     lang
--       ext2
--       par'
-- nf <***> nx = nf >>>= \(Fun f) -> nx >>>= \x -> embed (f x)

-- newtype Fun a b par = Fun {unFun :: a par -> b par}

instance Nomad PRFExt where
  type Par PRFExt n = KnownNat n
  embed = U.embed
  bindFN = U.bind
  nomap = U.extend

instance Nomad (Sum a) where
  type Par (Sum a) _ = ()
  embed = R
  bindFN f = \case
    L x -> L x
    R y -> f y
