{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.Antiguas.PRFExt
  (
    -- | Modulo interno principal que define las PRFs y reexporta los
    -- | tipos necesarios en otros modulos
    
    -- Funciones Recursivas Parciales (PRFs). Definicion del tipo
    -- general PRFExt que permite extender el lenguaje de las PRFs.
    PRFExt (..), PRFGen,

    -- Tipo suma con parametro natural
    Sum(..),

    -- Variante basica de las PRFs
    PRF, BasicaCons,

    -- Variante optimizada de las PRFs
    PRFRapida, OptimCons (..),
    pattern Cte, pattern Mas, pattern Menos,
    pattern Por, pattern Coc, pattern Res,

    -- Clase para evaluar las PRFs
    Evaluable,
    ev,

    -- Funcion para evaluar una PRF
    evalPRF, ($$),

    -- Se reexportan tipos y constructores utiles
    Natural,
    Proxy(..), Type,
    Finite, natToFinite,
    Vector, (//),
    Nat, KnownNat,
    type (+), type (-), type (<=),
  )
where

import Data.Proxy (Proxy(..))
import Data.Finite (Finite, natToFinite)
import Data.Kind (Type)
import Data.Vector.Sized (Vector, (//))
import qualified Data.Vector.Sized as V
import GHC.Natural (Natural)
import GHC.TypeNats

-- Plan para construir Funciones Recursivas Parciales (PRF)
-- Vease Cutland: Computability
data PRFExt :: (Nat -> Type) -> Nat -> Type where
  -- | FUNCIONES BASICAS. Para Z, he escogido la convencion de que es
  -- | una funcion 0-aria (o sea, una constante sin argumentos), de
  -- | manera que puedo obtener otras funciones 0-arias
  Z :: forall extension. PRFExt extension 0 -- Cte 0
  S :: forall ext. PRFExt ext 1 -- Funcion sucesor
  U :: forall n ext. KnownNat n => Finite n -> PRFExt ext n -- Proyeccion

  -- | OPERADORES BASICOS.
  -- | Sustitucion (generaliza la composicion):
  Subst ::
    forall m n ext.
    (KnownNat m, KnownNat n) =>
    PRFExt ext m ->
    Vector m (PRFExt ext n) ->
    PRFExt ext n

  -- | Recursividad Primitiva (tipo iteracion):
  -- | (Rec f g)(x1,...,xn, y) =
  -- | si y == 0 -> f(x1,...,xn)
  -- | si y >  0 -> g(x1,...,xn, y-1, (Rec f g)(x1,...,xn, y-1))
  Rec :: forall n ext. (KnownNat n) =>
    PRFExt ext n -> PRFExt ext (n + 2) -> PRFExt ext (n + 1) -- Recursividad

  -- | Minimalizacion, operador Mu:
  -- | Mu f(x1,...,xn, y) == Min z tal que f(x1,...,xn, z) = 0
  Mu :: forall n ext. (KnownNat n) => PRFExt ext (n + 1) -> PRFExt ext n

  -- | EXTRA: Para ampliar el lenguaje de manera sencilla
  Extra :: forall n ext. KnownNat n => ext n -> PRFExt ext n

-- Tipo suma con parametro natural
data Sum a b n = L (a n) | R (b n)

-- PRF Basicas, sin ningun extra: Usa el tipo vacio BasicaCons
data BasicaCons :: Nat -> Type

type PRF = PRFExt BasicaCons

-- PRFs arbitrarias
type PRFGen n = forall ext. PRFExt ext n

-- PRFs con optimizacion añadida al evaluar sumas, productos...
data OptimCons :: Nat -> Type where
  MkCte :: forall n. Natural -> OptimCons n -- Cte. natural n-aria
  MkMas :: OptimCons 2
  MkMenos :: OptimCons 2
  MkPor :: OptimCons 2
  MkCoc :: OptimCons 2  -- Cociente. Es 0 si el denominador es 0
  MkRes :: OptimCons 2  -- Cociente. Es 0 si el denominador es 0
  -- no voy a poner MkSg de momento

type PRFRapida = OptimCons

{-# COMPLETE Z, S, U, Subst, Rec, Mu, Cte, Mas, Menos, Por, Coc, Res #-}
pattern Cte :: forall (n :: Nat). () => KnownNat n => Natural -> PRFExt OptimCons n
pattern Cte m = Extra (MkCte m)
pattern Mas :: PRFExt OptimCons 2
pattern Mas = Extra MkMas
pattern Menos :: PRFExt OptimCons 2
pattern Menos = Extra MkMenos
pattern Por :: PRFExt OptimCons 2
pattern Por = Extra MkPor
pattern Coc :: PRFExt OptimCons 2
pattern Coc = Extra MkCoc
pattern Res :: PRFExt OptimCons 2
pattern Res = Extra MkRes

-- Clase para aquellas PRFs que se puedan evaluar
class Evaluable ext where
  ev :: (KnownNat n) => ext n -> Vector n Natural -> Natural

instance Evaluable OptimCons where
  -- Deberia evitar la pereza aqui
  ev (MkCte n) _ = n
  ev MkMas (head2 -> (x, y)) = x + y
  ev MkMenos (head2 -> (x, y)) = if x <= y then 0 else x - y
  ev MkPor (head2 -> (x, y)) = x * y
  ev MkCoc (head2 -> (x, y)) = if y == 0 then 0 else x `quot` y
  ev MkRes (head2 -> (x, y)) = if y == 0 then 0 else x `rem` y

-- No hay constructores => No hay nada que evaluar
instance Evaluable BasicaCons where
  ev = \case

-- Se hace `ev' un sinonimo de `evalPRF'
instance Evaluable ext => Evaluable (PRFExt ext) where
  ev = evalPRF

-- Para poder unir extensiones evaluables
instance (Evaluable ext1, Evaluable ext2) =>
    Evaluable (Sum ext1 ext2) where
  ev (L x) = ev x
  ev (R y) = ev y

-- Evalua la PRF dada en el vector de naturales dado
evalPRF, ($$) :: forall ext n. (KnownNat n, Evaluable ext) =>
  PRFExt ext n -> Vector n Natural -> Natural
evalPRF _f v = case _f of
  Z -> 0
  S -> V.head v + 1
  U m -> v `V.index` m
  Subst f gs -> evalPRF f (V.map (`evalPRF` v) gs)
  Mu f -> go 0 where
    go :: Natural -> Natural
    go n = case evalPRF f (v V.++ vec1 n) of
      0 -> n
      _ -> go (n + 1)
  Rec f g -> go (V.last v) where
    go :: Natural -> Natural
    go 0 = evalPRF f $ parameters
    go y = evalPRF g $ parameters V.++ vec2 (y - 1) (go $ y - 1)
    parameters = V.init v
  Extra f -> ev f v

-- Sinonimo util de `evalPRF' como operador
($$) = evalPRF

-- Funciones que definire en Data.PRF.Antiguas.Utils
-- fZero, fOne, fTwo dan 0, 1 como valor de Finite n
fZero :: (KnownNat n, 1 <= n) => Finite n
fZero = natToFinite $ Proxy @0
fOne  :: (KnownNat n, 2 <= n) => Finite n
fOne = natToFinite $ Proxy @1

-- dos primeros valores del vector
head2 :: (KnownNat n, 2 <= n) => Vector n a -> (a, a)
head2 v = (v `V.index` fZero, v `V.index` fOne)

-- Vectores pequenos
vec1 :: a -> Vector 1 a
vec1 = V.singleton
vec2 :: a -> a -> Vector 2 a
vec2 = curry V.fromTuple
