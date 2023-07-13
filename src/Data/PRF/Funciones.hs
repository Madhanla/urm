{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.PRF.Funciones
  ( -- | PRFs basicas lentas, ya que definen las operaciones
    -- | aritmeticas basicas de manera recursiva

    -- * Operaciones aritmeticas basicas
    mas,
    menos,
    por,
    quot',
    rem',
    -- quot'F,
    -- rem'F,

    -- * Proposiciones
    sg,
    sgbarra,
    desigualdad,
    igualdad,

    -- * Otras
    maximo,
    minimo,
    dist,
    cte,

    -- * Para usar operaciones aritmeticas con las PRFs
    NumLentoPRF (..),
  )
where

import Data.PRF.PRFExt

-- | Definición de NumLentoPRF, que hace que se puedan sumar y restar
-- funciones

newtype NumLentoPRF ext n = NL {unNL :: PRFExt ext n}

-- | Funciones básicas

-- Version lenta de Cte
cte :: forall ext n. KnownNat n => Natural -> PRFExt ext n
cte 0 = cte0
cte n = S .:. (vec1 . cte) (n - 1)

-- Version lenta de Mas
mas :: PRFExt ext 2
mas =
  Rec x0 (S .:. vec1 x2)

-- Version lenta de Por
por :: PRFExt ext 2
por =
  Rec cte0 (mas .:. vec2 x2 x0)

-- Version lenta de Menos
menos :: PRFExt ext 2
menos =
  Rec x0 (prd .:. vec1 x2)

-- Predecesorem'

prd :: PRFExt ext 1
prd = Rec Z x0

-- Minimos: Los pondre en un modulo aparte (?)
minimo :: PRFExt ext 2
minimo = menos .:. vec2 x0 (menos .:. vec2 x0 x1)

-- Maximos
maximo :: PRFExt ext 2
maximo = mas .:. vec2 x0 (menos .:. vec2 x1 x0)

-- Version lenta de Sg
sg :: PRFExt ext 1
sg = Rec cte0 (cte 1)

-- Sgbarra (negacion de sg)
sgbarra :: PRFExt ext 1
sgbarra = menos .:. vec2 (cte 1) sg

-- Distancia (valor absoluto de la diferencia)
dist :: PRFExt ext 2
dist = mas .:. vec2 (menos .:. vec2 x0 x1) (menos .:. vec2 x1 x0)

-- desigualdad
desigualdad :: PRFExt ext 2
desigualdad = sg .:. vec1 (dist .:. vec2 x0 x1)

-- igualdad
igualdad :: PRFExt ext 2
igualdad = sgbarra .:. vec1 desigualdad

-- Version lenta de Quot'
-- quot' = flipea quot'
quot' :: PRFExt ext 2
quot' =
  Rec cte0 $
    mas .:. vec2 x2 (igualdad .:. vec2 x0 anterior)
  where
    anterior = S .:. vec1 (rem' .:. vec2 x0 x1)

-- Version lenta de Rem' (F significa argumentos flipeados)
-- rem' = flipea rem'
rem' :: PRFExt ext 2
rem' =
  Rec cte0 $
    por .:. vec2 anterior (desigualdad .:. vec2 x0 anterior)
  where
    anterior = S .:. vec1 x2

-- | Instancia
instance KnownNat n => Num (NumLentoPRF ext n) where
  fromInteger = NL . cte . fromIntegral
  NL f + NL g = NL (mas .:. vec2 f g)
  NL f * NL g = NL (por .:. vec2 f g)
  abs = id -- los naturales son positivos

  -- Las diferencias negativas se hacen 0
  NL f - NL g = NL (menos .:. vec2 f g)

  -- Negar se hace entendiendo 1 como Verdadero, 0 como Falso
  negate (NL f) = NL (sgbarra .:. vec1 f)

  -- Signum es Sg
  signum (NL f) = NL (sg .:. vec1 f)
