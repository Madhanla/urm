{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.Antiguas.Basica
  ( -- Funciones definidas principalmente para la PRF basica: son mas
    -- lentas que las definidas en otros modulos. Tambien defino
    -- funciones de ayuda en la escritura de PRFs.

    -- Funciones generales para cualquier extension de las PRFs
    ident,
    cte0,
    -- Funciones (PRFs) basicas lentas
    cte,
    mas,
    menos,
    por,
    coc,
    res,
    cocF,
    resF,
    sg,
    sgbarra,
    dist,
    desigualdad,
    igualdad,
    maximo,
    minimo,
  )
where

import Data.PRF.Antiguas.PRFExt
import Data.PRF.Antiguas.Utils

-- Version lenta de Cte
cte :: forall n ext. KnownNat n => Natural -> PRFExt ext n
cte 0 = cte0
cte n = Subst S (vec1 . cte $ n - 1)

-- Version lenta de Mas
mas :: PRFGen 2
mas =
  Rec (U fZero) $
    useArgs (vec1 fTwo) S

-- Version lenta de Por
por :: PRFGen 2
por =
  Rec cte0 $
    useArgs
      (vec2 fTwo fZero)
      mas

-- Version lenta de Menos
menos :: PRFGen 2
menos =
  Rec (U fZero) $
    useArgs
      (vec1 fTwo)
      prd

-- Predecesores

prd :: PRFGen 1
prd = Rec Z $ (U fZero)

-- Minimos: Los pondre en un modulo aparte
minimo :: PRFGen 2
minimo =
  Subst menos $
    vec2
      (U fZero)
      (Subst menos $ vec2 (U fZero) (U fOne))

-- Maximos
maximo :: PRFGen 2
maximo =
  Subst mas $
    vec2
      (U fZero)
      (Subst menos $ vec2 (U fOne) (U fZero))

-- Version lenta de Sg
sg :: PRFGen 1
sg = Rec cte0 $ cte 1

-- Sgbarra (negacion de sg)
sgbarra :: PRFExt ext 1
sgbarra = Subst menos $ vec2 (cte 1) sg

-- Distancia
dist :: PRFGen 2
dist =
  Subst mas $
    vec2
      (useArgs (vec2 fZero fOne) menos)
      (useArgs (vec2 fOne fZero) menos)

-- desigualdad
desigualdad :: PRFGen 2
desigualdad = Subst sg $ vec1 $ useArgs (vec2 fZero fOne) dist

-- igualdad
igualdad :: PRFGen 2
igualdad = Subst menos $ vec2 (cte 1) desigualdad

-- Version lenta de Coc
cocF, coc :: PRFGen 2
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
resF, res :: PRFGen 2
resF =
  Rec cte0 $
    Subst por $
      vec2
        rm
        (Subst desigualdad (vec2 (U fZero) rm))
  where
    rm = useArgs (vec1 fTwo) S
res = flipea resF
