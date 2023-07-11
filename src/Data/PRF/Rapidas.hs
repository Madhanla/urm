{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Data.PRF.Rapidas
  ( -- Modulo de definicion de un lenguaje aritmetico con idea de
    -- extender el lenguaje de las PRFs y hacerlo mas rapido
    AritLang (..),
    PRFRapida,
    pattern RapCte,
    pattern RapMas,
    pattern RapMenos,
    pattern RapPor,
    pattern RapCoc,
    pattern RapRes,
  )
where

import Data.PRF.Clases
import Data.PRF.Funciones
-- import Data.PRF.Lang
import Data.PRF.PRFExt

-- | Lenguaje aritmetico con naturales.
-- * Cte construye una funcion constante n-aria.
-- * Mas construye la funcion suma binaria
-- * Menos construye la diferencia binaria, con y - x = 0 si y < x
-- * Por construye el producto binario
-- * Coc construye el cociente binario, que vale 0 si el denominador
--   es 0
-- * Res construye el resto binario, que vale 0 si el denominador es 0
data AritLang :: Nat -> Type where
  Cte :: forall n. KnownNat n => Natural -> AritLang n -- Cte. natural n-aria
  Mas :: AritLang 2
  Menos :: AritLang 2
  Por :: AritLang 2
  Coc :: AritLang 2
  Res :: AritLang 2

-- Este es el lenguaje en el que me centrare en Data.PRF.Rapidas.*
-- Por eso usare algunos sinonimos utiles
type PRFRapida = PRFExt AritLang

{-# COMPLETE
  Z,
  S,
  U,
  Subst,
  Rec,
  Mu,
  RapCte,
  RapMas,
  RapMenos,
  RapPor,
  RapCoc,
  RapRes
  #-}

pattern RapCte :: () => KnownNat n => Natural -> PRFRapida n
pattern RapCte x = Extra (Cte x)

pattern RapMas :: PRFRapida 2
pattern RapMas = Extra Mas

pattern RapMenos :: PRFRapida 2
pattern RapMenos = Extra Menos

pattern RapPor :: PRFRapida 2
pattern RapPor = Extra Por

pattern RapCoc :: PRFRapida 2
pattern RapCoc = Extra Coc

pattern RapRes :: PRFRapida 2
pattern RapRes = Extra Res

instance Evaluable AritLang where
  -- Deberia evitar la pereza aqui
  eval (Cte n) _ = n
  eval Mas (head2 -> (x, y)) = x + y
  eval Menos (head2 -> (x, y)) = if x <= y then 0 else x - y
  eval Por (head2 -> (x, y)) = if y == 0 then 0 else x * y
  eval Coc (head2 -> (x, y)) = if y == 0 then 0 else x `quot` y
  eval Res (head2 -> (x, y)) = if y == 0 then 0 else x `rem` y

instance ToPRF AritLang where
  -- El lenguaje rapido se puede convertir al de las PRFs a costa de
  -- la rapidez
  toPRF = \case
    Cte n -> cte n
    Mas -> mas
    Menos -> menos
    Por -> por
    Coc -> coc
    Res -> res

instance ExtPrimit AritLang where
  -- Este lenguaje no anade funciones no recursivas primitivas
  esPrimitivaRecursiva = const True

instance KnownNat m => Show (AritLang m) where
  show = \case
    Cte n -> "Cte" ++ m ++ "(" ++ show n ++ ")"
    Mas -> "Mas2"
    Menos -> "Menos2"
    Por -> "Por2"
    Coc -> "Coc2"
    Res -> "Res2"
    where
      m = show $ natVal (Proxy @m)

instance KnownNat n => Num (PRFRapida n) where
  fromInteger x = RapCte . fromInteger $ x
  f + g = Subst RapMas (vec2 f g)
  f * g = Subst RapPor (vec2 f g)
  f - g = Subst RapMenos (vec2 f g)
  abs = id
  negate f = 1 - f
  signum = negate . negate
