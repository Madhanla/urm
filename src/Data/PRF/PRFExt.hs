{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.PRFExt
  ( -- | Modulo interno principal que define las PRFs y reexporta los
    -- | tipos necesarios en otros modulos

    -- * Tipo para las Funciones Primitivas Parciales (PRFs), y
    --   funciones para evaluarlas
    PRFExt (..), PRF,
    Evaluable (..),
    evalPRF, ($$),

    -- * PRFs basicas y funciones de ayuda en la escritura de PRFs
    ident, cte0,
    useArgs, flipea,
    bott,

    -- * Funciones utiles para trabajar con vectores y finitos
    fZero, fOne, fTwo, fThree,
    head2, head3,
    vec0, vec1, vec2, vec3, vec4,
    finites,
    
    -- * Se reexportan tipos y constructores utiles.

    -- Functores y monadas con parametros
    HSum (..),
    HMonad (..), HFunctor (..),

    -- Kinds
    Type, Constraint,

    -- Nats (naturales en los tipos)
    Proxy (..), Nat, KnownNat,
    type (+), type (-), type (<=),
    natVal,

    -- Naturales
    Natural,

    -- Vectores y Finitos
    Finite, natToFinite,
    Vector, (//),
  )
where

import Data.Finite (Finite, natToFinite)
import Data.Kind (Constraint, Type)
import Data.PRF.Lang
import Data.Proxy (Proxy (..))
import Data.Vector.Sized (Vector, (//))
import qualified Data.Vector.Sized as V
-- import qualified Data.Finite as F
import GHC.Natural (Natural)
import GHC.TypeNats

-- Plan para construir Funciones Recursivas Parciales (PRF)
-- Vease Cutland: Computability
data PRFExt :: (Nat -> Type) -> Nat -> Type where
  --  * FUNCIONES BASICAS: S (sucesor), Z (cte. 0) y U (proyeccion). Para
  --  Z, he escogido la convencion de que es una funcion 0-aria (o sea,
  --  una constante sin argumentos), de manera que puedo obtener otras
  --  funciones 0-arias.
  --
  --  * OPERADORES BASICOS: Subst (sustitucion), Rec (recursividad
  --  primitiva) y Mu (minimalizacion).
  --
  --  Sustitucion (generaliza la composicion):
  --  (Subst h (g1,...,gm))(x1,...,xn) = h(g1(x1,...,xn), ..., gm(x1,...,xn))
  --
  --  Recursividad Primitiva (tipo iteracion):
  --  (Rec f g)(x1,...,xn, y) =
  --  si y == 0 -> f(x1,...,xn)
  --  si y >  0 -> g(x1,...,xn, y-1, (Rec f g)(x1,...,xn, y-1))
  --
  --  Minimalizacion, operador Mu:
  --  Mu f(x1,...,xn, y) == Min z tal que f(x1,...,xn, z) = 0
  --
  --  Nota: seria interesante cambiar el tipo de Rec, Subst, Mu para
  --  que salgan directamente de ext n en vez de PRFExt n, y poder asi
  --  usar la suma (HSum) en vez del constructor Extra. El actual
  --  PRFExt seria aproximadamente el tipo parcialmente aplicado (HSum
  --  PRF), aunque seria necesario usar un punto fijo para usar el
  --  lenguaje
  --
  --  * EXTENSIONES: Se anaden extensiones con el constructor Extra
  --
  Z :: PRFExt ext 0
  S :: PRFExt ext 1
  U :: forall ext n. KnownNat n => Finite n -> PRFExt ext n

  Subst :: forall ext m n. (KnownNat m, KnownNat n) =>
    PRFExt ext m -> Vector m (PRFExt ext n) -> PRFExt ext n

  Rec :: forall ext n. KnownNat n =>
    PRFExt ext n -> PRFExt ext (n + 2) -> PRFExt ext (n + 1)

  Mu :: forall ext n. KnownNat n => PRFExt ext (n + 1) -> PRFExt ext n

  Extra :: forall ext n. KnownNat n => ext n -> PRFExt ext n

-- PRF sin extensiones
type PRF = PRFExt EmptyExt

-- Clase para aquellos lenguajes que se puedan evaluar como una
-- funcion N^n -> N
class Evaluable lang where
  eval :: KnownNat n => lang n -> Vector n Natural -> Natural

instance Evaluable ext => Evaluable (PRFExt ext) where
  eval = evalPRF

instance Evaluable EmptyExt where
  eval = \case

-- Para poder unir lenguajes evaluables
instance
  (Evaluable lang1, Evaluable lang2) =>
  Evaluable (HSum lang1 lang2)
  where
  -- eval = heither @lang1 @lang2 eval eval
  eval = heither eval eval

-- Para poder evaluar lenguajes anidados
instance (forall ext. Evaluable ext => Evaluable (lang ext)) =>
  Evaluable (HFix lang) where
  eval (F x) = eval x

-- Evalua una PRF en un vector de naturales dado
evalPRF, ($$) :: forall ext n. (Evaluable ext, KnownNat n) =>
  PRFExt ext n -> Vector n Natural -> Natural
evalPRF _f v = case _f of
  Z -> 0
  S -> V.head v + 1
  U m -> v `V.index` m
  Subst f gs -> evalPRF f (V.map (`evalPRF` v) gs)
  Mu f -> go 0
    where
      go :: Natural -> Natural
      go n = case evalPRF f (v V.++ vec1 n) of
        0 -> n
        _ -> go (n + 1)
  Rec f g -> go (V.last v)
    where
      go :: Natural -> Natural
      go 0 = evalPRF f $ parameters
      go y = evalPRF g $ parameters V.++ vec2 (y - 1) (go $ y - 1)
      parameters = V.init v
  Extra f -> eval f v

-- Sinonimo util de evalPRF como operador
($$) = evalPRF

-- | Funciones utiles variadas


-- * PRFs sencillas 
-- Función identidad
ident :: forall ext. PRFExt ext 1
ident = U fZero

-- cte 0 n-aria
cte0 :: forall ext n. KnownNat n => PRFExt ext n
cte0 = useArgs V.empty Z

-- funcion no definida en ninguna parte
bott :: forall ext n. KnownNat n => PRFExt ext n
bott = Mu (Subst S (vec1 cte0))

-- * FUNCIONES para ayudar en la escritura de PRFs.

-- useArgs sustituye las variables de una funcion f n-aria por las que
-- vienen dadas por el vector v para obtener una funcion m-aria.
-- useArgs @3 @4 f(x1,x2,x3) (2,2,4) = f(y2, y2, y4)
useArgs :: forall ext m n. (KnownNat m, KnownNat n)
  => Vector m (Finite n) -> PRFExt ext m -> PRFExt ext n
useArgs v f = Subst f (V.map U v)

-- flipea argumentos
flipea :: forall ext. PRFExt ext 2 -> PRFExt ext 2
flipea = useArgs $ V.fromTuple (fOne, fZero)

-- fZero, fOne, fTwo dan 0, 1 ó 2 como valor de Finite n
fZero :: (KnownNat n, 1 <= n) => Finite n
fZero = natToFinite $ Proxy @0
fOne  :: (KnownNat n, 2 <= n) => Finite n
fOne = natToFinite $ Proxy @1
fTwo :: (KnownNat n, 3 <= n) => Finite n
fTwo = natToFinite $ Proxy @2
fThree :: (KnownNat n, 4 <= n) => Finite n
fThree = natToFinite $ Proxy @3

-- head2, head3 toman un vector lo bastante grande y devuelven sus
-- primeros elementos en una tupla
head2 :: (KnownNat n, 2 <= n) => Vector n a -> (a, a)
head2 v = (v `V.index` fZero, v `V.index` fOne)
head3 :: (KnownNat n, 3 <= n) => Vector n a -> (a, a, a)
head3 v = (v `V.index` fZero, v `V.index` fOne, v `V.index` fTwo)

-- Vectores pequenos
vec0 :: Vector 0 a
vec0 = V.empty
vec1 :: a -> Vector 1 a
vec1 = V.singleton
vec2 :: a -> a -> Vector 2 a
vec2 = curry V.fromTuple
vec3 :: a -> a -> a -> Vector 3 a
vec3 x y z = V.fromTuple (x, y, z)
vec4 :: a -> a -> a -> a -> Vector 4 a
vec4 x y z w = V.fromTuple (x, y, z, w)

-- Vector con todos los finitos
finites :: KnownNat n => Vector n (Finite n)
finites = V.generate id
-- finites = case V.fromList F.finites of 
-- Just v -> v
-- Nothing -> error "Error en la implementacion de `finites'"

-- Instancias
instance HFunctor PRFExt where
  type Par PRFExt n = KnownNat n
  hmap f = hbind (hreturn . f)  -- Por defecto

instance HMonad PRFExt where
  hreturn :: KnownNat n => ext n -> PRFExt ext n
  hreturn = Extra

  hbind :: forall ext1 ext2 n.
    (forall m. KnownNat m => ext1 m -> PRFExt ext2 m) ->
    PRFExt ext1 n -> PRFExt ext2 n
  hbind phi = go where
    go :: forall n0. PRFExt ext1 n0 -> PRFExt ext2 n0
    go = \case {Z -> Z; S -> S; U k -> U k;
    Subst f hs -> Subst (go f) (V.map go hs);
    Rec f g -> Rec (go f) (go g);
    Mu f -> Mu (go f);
    Extra f -> phi f}

-- No funciona bien con puntos fijos
instance (KnownNat n, forall m. KnownNat m => Show (ext m)) =>
  Show (PRFExt ext n) where
  show = \case
    Z -> "Z0"
    S -> "S1"
    (U k) -> "U" ++ n ++ "_" ++ show (fromIntegral k + 1 :: Integer)
    (Subst f g) -> "Subst" ++ n ++ "(" ++ show f ++ ", " ++ show g ++ ")"
    (Rec f g) -> "Rec" ++ n ++ "(" ++ show f ++ ", " ++ show g ++ ")"
    (Mu f) -> "Mu" ++ n ++  "(" ++ show f ++ ")"
    (Extra f) -> "Extra(" ++ show f ++ ")"
    where n = show . natVal $ Proxy @n
