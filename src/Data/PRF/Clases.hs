{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.Clases
  ( -- | Modulo que define clases interesantes relacionadas con las
    -- | PRFs

    -- * Clase de lenguajes que se pueden transformar en el de las PRFs
    ToPRF (..),

    -- * Clase de lenguajes que extienden a las funciones recursivas

    --   primitivas
    ExtPrimit (..),
  )
where

import Data.PRF.Lang
import Data.PRF.PRFExt

class ToPRF lang where
  -- Clase para los lenguajes que se pueden convertir en PRFs
  -- basicas. Si son tambien de la clase Evaluable, deben cumplir:
  -- evalPRF f v == evalPRF (toBasica f) v
  toPRF :: KnownNat n => lang n -> PRF n

class ExtPrimit lang where
  -- Clase para los lenguajes que contienen algunas funciones
  -- recursivas primitivas y una forma de asegurar que una funcion es
  -- primitiva recursiva. Es necesario permitir los falsos negativos,
  -- por el teorema de Rice.
  esPrimitivaRecursiva :: KnownNat n => lang n -> Bool

instance ToPRF ext => ToPRF (PRFExt ext) where
  toPRF = hbind toPRF

instance ToPRF EmptyExt where
  toPRF = \case {}

instance (ToPRF lang1, ToPRF lang2) => ToPRF (HSum lang1 lang2) where
  toPRF = heither toPRF toPRF

instance (forall ext. ToPRF ext => ToPRF (lang ext)) => ToPRF (HFix lang) where
  toPRF (F x) = toPRF x

instance ExtPrimit ext => ExtPrimit (PRFExt ext) where
  esPrimitivaRecursiva = \case
    Z -> True
    S -> True
    U _ -> True
    Subst f v -> all esPrimitivaRecursiva v && esPrimitivaRecursiva f
    Rec f g -> esPrimitivaRecursiva f && esPrimitivaRecursiva g
    Mu _ -> False
    Extra f -> esPrimitivaRecursiva f

instance ExtPrimit EmptyExt where
  esPrimitivaRecursiva = \case {}

instance (ExtPrimit lang1, ExtPrimit lang2) => ExtPrimit (HSum lang1 lang2) where
  esPrimitivaRecursiva = heither esPrimitivaRecursiva esPrimitivaRecursiva

instance (forall ext. ExtPrimit ext => ExtPrimit (lang ext)) => ExtPrimit (HFix lang) where
  esPrimitivaRecursiva (F x) = esPrimitivaRecursiva x
