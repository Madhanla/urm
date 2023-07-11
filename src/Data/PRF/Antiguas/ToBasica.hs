{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.ToBasica
  ( -- Clase para indicar que una extension de PRFs es redundante, ya
    -- que se puede convertir en una PRF Basica.
    ToBasica,
    toBasica,
  )
where

import Data.PRF.Antiguas.Basica
import Data.PRF.Antiguas.PRFExt
import Data.PRF.Antiguas.Utils

-- import qualified Data.Vector.Sized as V

-- Clase para las extensiones de PRFs que se pueden convertir en
-- PRFs Basicas. Si son tambien de la clase Evaluable, deben cumplir:
-- evalPRF f v == evalPRF (toBasica f) v
class ToBasica ext where
  toBasica :: KnownNat n => ext n -> PRF n

instance ToBasica BasicaCons where
  toBasica = \case {}

instance ToBasica OptimCons where
  toBasica = \case
    MkCte n -> cte n
    MkMas -> mas
    MkMenos -> menos
    MkPor -> por
    MkCoc -> coc
    MkRes -> res

instance ToBasica ext => ToBasica (PRFExt ext) where
  toBasica = bind toBasica

-- | Manera original de hacerlo, mas larga
--   toBasica = \case
--     Z -> Z
--     S -> S
--     U k -> U k
--     Subst f hs -> Subst (toBasica f) (V.map toBasica hs)
--     Rec g h -> Rec (toBasica g) (toBasica h)
--     Mu f -> Mu (toBasica f)
--     Extra f -> toBasica f
instance
  (ToBasica ext1, ToBasica ext2) =>
  ToBasica (Sum ext1 ext2)
  where
  toBasica (L x) = toBasica x
  toBasica (R y) = toBasica y
