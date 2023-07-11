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
    coc,
    res,
    cocF,
    resF,

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

newtype NumLentoPRF ext n = NL {unNL :: PRFExt ext n}

-- Version lenta de Cte
cte :: forall ext n. KnownNat n => Natural -> PRFExt ext n
cte 0 = cte0
cte n = Subst S (vec1 . cte $ n - 1)

-- Version lenta de Mas
mas :: PRFExt ext 2
mas =
  Rec (U fZero) $
    useArgs (vec1 fTwo) S

-- Version lenta de Por
por :: PRFExt ext 2
por =
  Rec cte0 $
    useArgs
      (vec2 fTwo fZero)
      mas

-- Version lenta de Menos
menos :: PRFExt ext 2
menos =
  Rec (U fZero) $
    useArgs
      (vec1 fTwo)
      prd

-- Predecesores

prd :: PRFExt ext 1
prd = Rec Z $ (U fZero)

-- Minimos: Los pondre en un modulo aparte
minimo :: PRFExt ext 2
minimo =
  Subst menos $
    vec2
      (U fZero)
      (Subst menos $ vec2 (U fZero) (U fOne))

-- Maximos
maximo :: PRFExt ext 2
maximo =
  Subst mas $
    vec2
      (U fZero)
      (Subst menos $ vec2 (U fOne) (U fZero))

-- Version lenta de Sg
sg :: PRFExt ext 1
sg = Rec cte0 $ cte 1

-- Sgbarra (negacion de sg)
sgbarra :: PRFExt ext 1
sgbarra = Subst menos $ vec2 (cte 1) sg

-- Distancia
dist :: PRFExt ext 2
dist =
  Subst mas $
    vec2
      (useArgs (vec2 fZero fOne) menos)
      (useArgs (vec2 fOne fZero) menos)

-- desigualdad
desigualdad :: PRFExt ext 2
desigualdad = Subst sg $ vec1 $ useArgs (vec2 fZero fOne) dist

-- igualdad
igualdad :: PRFExt ext 2
igualdad = Subst menos $ vec2 (cte 1) desigualdad

-- Version lenta de Coc
cocF, coc :: PRFExt ext 2
cocF =
  Rec cte0 $
    Subst mas $
      vec2
        (U fTwo)
        ( Subst igualdad $
            vec2
              (U fZero)
              (Subst S $ vec1 $ useArgs (vec2 fZero fOne) resF)
        )
coc = flipea cocF

-- Version lenta de Res (F significa argumentos flipeados)
resF, res :: PRFExt ext 2
resF =
  Rec cte0 $
    Subst por $
      vec2
        rm
        (Subst desigualdad (vec2 (U fZero) rm))
  where
    rm = useArgs (vec1 fTwo) S
res = flipea resF

instance KnownNat n => Num (NumLentoPRF ext n) where
  fromInteger = NL . cte . fromIntegral
  NL f + NL g = NL . Subst mas $ vec2 f g
  NL f * NL g = NL . Subst por $ vec2 f g
  abs = id -- los naturales son positivos

  -- Las diferencias negativas se hacen 0
  NL f - NL g = NL . Subst menos $ vec2 f g

  -- Negar se hace entendiendo 1 como Verdadero, 0 como Falso
  negate f = 1 - f

  -- Signum es Sg
  signum (NL f) = NL . Subst sg $ vec1 f
