{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF
  -- AVISO. Esta hecho de otra manera mejor en Data.PRF.PRF
  ( -- | Definicion de las funciones recursivas parciales (PRF)
    -- | y funciones necesarias para las instancias basicas
    -- | (Show, Num)

    -- Solo se exportan los constructores basicos que no cambiaran. A
    -- los eficientes se accede mediante las funciones definidas en
    -- este modulo.
    PRF(Z, S, U, Subst, Rec, Mu),

    -- Funciones constructor
    cte, mas, por, menos, coc, res, sg,

    -- Evaluar una PRF
    evalPRF, ($$),

    -- Funciones utiles variadas
    cte0, prd, ident, dist, desigualdad, igualdad, 

    -- Funciones para decidir si optar por la optimizacion
    esLenta, aLenta,

    -- Funciones recursivas primitivas (no usan la minimalizacion)
    esPrimitivaRecursiva,

    -- Comprobaciones
    pruebaDivision,

    -- No exporto las funciones lentas, pero se obtienen
    -- aplicando 'aLenta' a las correspondientes versiones eficientes.
    -- sg', cte', mas', por', menos', coc', res', prd', ..


    -- Se reexportan por comodidad tipos y constructores necesarios
    V.Vector( ),
    Finite( ),
    Proxy(..),
    Nat( ), type (<=), type (-), type (+), KnownNat, natVal,

    -- Funciones de ayuda
    fZero, fOne, fTwo,
    head2, head3,
    vec1, vec2, vec3, vec4,
    (...),
)
where

import Data.Finite (Finite( ), natToFinite)
import Data.Proxy (Proxy (..))
import Data.Vector.Sized (Vector( ), (//))
import qualified Data.Vector.Sized as V
import GHC.Natural (Natural(..))
import GHC.TypeNats -- (Nat( ), type (<=), type (-), type (+), KnownNat( ), natVal)

-- Plan para construir Funciones Recursivas Parciales (PRF)
-- Vease Cutland: Computability
data PRF (n :: Nat) where
  -- | FUNCIONES BASICAS. Para Z, he escogido la convencion de que es
  -- una funcion 0-aria (o sea, una constante sin argumentos), de
  -- manera que puedo obtener otras funciones 0-arias
  Z :: PRF 0 -- Representa la funcion constante 0 : N
  S :: PRF 1 -- Funcion sucesor N -> N
  U :: forall n. KnownNat n => Finite n -> PRF n -- Proyeccion (m+1)-esima N^n -> N

  -- | OPERADORES BASICOS.
  -- Sustitucion (generaliza la composicion):
  -- (Subst h (g1,...,gm))(x1,...,xn) = h(g1(x1,...,xn), ..., gm(x1,...,xn))
  Subst :: forall m n. (KnownNat m, KnownNat n) => PRF m -> Vector m (PRF n) -> PRF n -- Sustitucion

  -- Recursividad Primitiva (tipo iteracion):
  -- (Rec f g)(x1,...,xn, y) =
  -- si y == 0 -> f(x1,...,xn)
  -- si y >  0 -> g(x1,...,xn, y-1, (Rec f g)(x1,...,xn, y-1))
  Rec :: forall n. (KnownNat n) => PRF n -> PRF (n + 2) -> PRF (n + 1) -- Recursividad

  -- Minimalizacion, operador Mu:
  -- Mu f(x1,...,xn, y) == Min z tal que f(x1,...,xn, z) = 0
  Mu :: forall n. (KnownNat n) => PRF (n+1) -> PRF n

  -- CONSTRUCTORES EXTRA para aumentar la eficiencia
  Cte :: forall n. Natural -> PRF n -- Constante natural n-aria
  Mas :: PRF 2 -- Suma rapida
  Por :: PRF 2 -- Producto rapido
  Menos :: PRF 2 -- Diferencia rapida total (x-y = 0 si y > x)
  Coc :: PRF 2 -- Cociente rapido; por convencion el cociente entre 0 es 0.
  Res :: PRF 2 -- Resto rapido: x == Coc(x,y)*y + Res(x,y); salvo Res(x, 0) = 0
  Sg :: PRF 1 -- Sg(x) = 1 si x > 0; 0 si no. No se pa que la he anadido.

-- Las funciones que acaban en «'» son verisones lentas de las que
-- acaban sin la prima

mas, por, menos, coc, res :: PRF 2
mas = Mas; por = Por; menos = Menos; coc = Coc; res = Res
sg :: PRF 1
sg = Sg
cte :: forall n. Natural -> PRF n
cte = Cte

instance KnownNat n => Show (PRF n) where
  show Z = "Z0"
  show S = "S1"
  show (U k) = "U" ++ n ++ "_" ++ show (fromIntegral k + 1 :: Integer)
    where n = show . natVal $ Proxy @n
  show (Subst f g) = "Subst" ++ n ++ "(" ++ show f ++ ", " ++ show g ++ ")"
    where n = show . natVal $ Proxy @n
  show (Rec f g) = "Rec" ++ n ++ "(" ++ show f ++ ", " ++ show g ++ ")"
    where n = show . natVal $ Proxy @n
  show (Mu f) = "Mu" ++ n ++  "(" ++ show f ++ ")"
    where n = show . natVal $ Proxy @n
  show (Cte n) = "Cte2(" ++ show n ++ ")"
  show Mas = "Mas2"
  show Por = "Por2"
  show Menos = "Menos2"
  show Coc = "Coc2"
  show Res = "Res2"
  show Sg = "Sg1"

instance KnownNat n => Num (PRF n) where
  fromInteger = Cte . fromIntegral
  f + g = Subst Mas   $ vec2 f g
  f * g = Subst Por   $ vec2 f g
  abs = id -- los naturales son positivos
  
  -- Las diferencias negativas se hacen 0
  f - g = Subst Menos $ vec2 f g
  -- Negar se hace entendiendo 1 como Verdadero, 0 como Falso
  negate f = 1 - f
  -- Signum es Sg
  signum f = Subst Sg $ vec1 f

-- Ejemplo de funcion
-- x2xy2xz2y :: PRF 3 -> PRF 2
-- x2xy2xz2y f =
--   Subst f $ vec3 (U fZero) (U fZero) (U fOne)

-- Función identidad
ident :: PRF 1
ident = U fZero

-- cte 0 n-aria
cte0 :: forall n. KnownNat n => PRF n
cte0 = useArgs V.empty Z

-- Version lenta de Cte
cte' :: forall n. KnownNat n => Natural -> PRF n
cte' 0 = cte0
cte' n = Subst S (vec1 . cte' $ n - 1)

-- Version lenta de Mas
mas' :: PRF 2
mas' =
  Rec (U fZero) $
    useArgs (vec1 fTwo) S

-- Version lenta de Por
por' :: PRF 2
por' =
  Rec cte0 $ useArgs
      (vec2 fTwo fZero)
      mas'

-- Version lenta de Menos
menos' :: PRF 2
menos' = Rec (U fZero) $
    useArgs
      (vec1 fTwo)
      prd'

-- Predecesores

prd' :: PRF 1
prd' = Rec Z $ (U fZero)

prd  :: PRF 1
prd  = Subst Menos $ vec2 (U fZero) (Cte 1)

-- Minimos: Los pondre en un modulo aparte
-- minimo  :: PRF 2
-- minimo  = Subst Menos  $ vec2
--   (U fZero)
--   (Subst Menos  $ vec2 (U fZero) (U fOne))
--   
-- minimo' :: PRF 2
-- minimo' = Subst menos' $ vec2
--   (U fZero)
--   (Subst menos' $ vec2 (U fZero) (U fOne))
-- 
-- Maximos
-- maximo  :: PRF 2
-- maximo  = Subst Mas $ vec2
--   (U fZero) (Subst Menos $ vec2 (U fOne) (U fZero))
-- 
-- maximo' :: PRF 2
-- maximo' = Subst mas' $ vec2
--   (U fZero) (Subst menos' $ vec2 (U fOne) (U fZero))
-- 

-- Version lenta de Sg
sg' :: PRF 1
sg' = Rec cte0 $ cte' 1

-- Sgbarra (negacion de sg)
-- sgbarra', sgbarra :: PRF 1
-- sgbarra = negate Sg
-- sgbarra'  = Subst menos' $ vec2 (cte' 1) sg

-- Distancia
dist  :: PRF 2
dist  = Subst Mas $ vec2
  (useArgs (vec2 fZero fOne)  Menos)
  (useArgs (vec2 fOne  fZero) Menos)

dist' :: PRF 2
dist' = Subst mas' $ vec2
  (useArgs (vec2 fZero fOne)  menos')
  (useArgs (vec2 fOne  fZero) menos')

-- desigualdad
desigualdad, desigualdad'  :: PRF 2
desigualdad  = Subst Sg  $ vec1 $ useArgs (vec2 fZero fOne) dist
desigualdad' = Subst sg' $ vec1 $ useArgs (vec2 fZero fOne) dist'

-- igualdad
igualdad', igualdad :: PRF 2
igualdad  = negate desigualdad
igualdad' = Subst menos' $ vec2 (cte' 1) desigualdad'

-- Version lenta de Coc
cocF', coc' :: PRF 2
cocF' = Rec cte0 $
  Subst mas' $ vec2
    (U fTwo)
    (Subst igualdad' $ vec2
       (U fZero)
       (Subst S $ vec1 $ useArgs (vec2 fZero fOne) resF'))
coc' = flipea cocF'

-- Version lenta de Res (F significa argumentos flipeados)
resF', res' :: PRF 2
resF' = Rec cte0 $ Subst por' $ vec2
      rm'
      (Subst desigualdad' (vec2 (U fZero) rm'))
  where rm' = useArgs (vec1 fTwo) S
res' = flipea resF'

-- Evalúa la PRF dada.
evalPRF :: forall n. KnownNat n => PRF n -> Vector n Natural -> Natural
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
  Rec f g -> go v
    where
      -- v:(x0,...,x(n-2), y)
      -- f (x0,...,x(n-2))
      -- g (x0,...,x(n-2), y-1, (Rec .....))
      go :: Vector n Natural -> Natural
      go w =  case V.last w of
              0 -> evalPRF f $ (V.init w :: Vector (n - 1) Natural)
              y ->
                evalPRF g $
                  (prevList V.++ vec1 (go prevList) :: Vector (n + 1) Natural)
                where
                  prevList = w // [(nMinus1, y - 1)] :: Vector n Natural
                  nMinus1 = natToFinite $ Proxy @(n - 1)
  Cte n -> n
  Mas -> let (v1, v2) = head2 v in v1 + v2

  -- Compruebo si el primer argumento es 0 en el producto para no tener
  -- que evaluar el segundo; asi la implementacion de signum no efectua
  -- operaciones innecesarias. Cambiar luego para que funcione mejor.
  -- Ahora mismo no hace eso
  Por -> let (v1, v2) = head2 v in v1 * v2
  Menos -> let (v1, v2) = head2 v
   in case compare v1 v2 of
        GT -> v1 - v2
        _  -> 0
  Coc -> let (v1, v2) = head2 v
   in case v2 of
        0 -> 0
        _ -> v1 `quot` v2
  Res -> let (v1, v2) = head2 v
   in case v2 of
        0 -> 0
        _ -> v1 `rem` v2
  Sg -> let y = V.head v in signum y

-- Version operador de evalPRF
infix 1 $$
($$) :: forall n. KnownNat n => PRF n -> Vector n Natural -> Natural
($$) = evalPRF

-- | ES LENTA? CONVERTIR A LENTA
-- Comprueba que una PRF no usa la optimizacion.
esLenta :: forall n. KnownNat n => PRF n -> Bool
esLenta _f = case _f of
  {Cte _ -> False; Mas -> False; Menos -> False; Por -> False;
   Coc -> False; Res -> False; Sg -> False;
   Z -> True; S -> True; U _ -> True;
   Subst f v -> and (V.map esLenta v) && esLenta f;
   Rec f g -> esLenta f && esLenta g;
   Mu f -> esLenta f;
  }

-- La optimizacion debe ser prescindible; aLenta se deshace de
-- ella. Debe ser idempotente (aLenta . aLenta == aLenta), y además
-- debe ocurrir (esLenta . aLenta == const True).
aLenta :: forall n. KnownNat n => PRF n -> PRF n
aLenta _f = case _f of
  {Cte x -> cte' x; Mas -> mas'; Menos -> menos'; Por -> por';
   Coc -> coc'; Res -> res'; Sg -> sg';
   Z -> Z; S -> S; u@(U _) -> u;
   Subst f v -> Subst (aLenta f) (V.map aLenta v);
   Rec f g -> Rec (aLenta f) (aLenta g);
   Mu f -> Mu (aLenta f);
  }

-- | PRIMITIVA RECURSIVA. No existe un algoritmo que nos permita
-- dilucidar si una PRF es primitiva recursiva (por el Teorema de
-- Rice). Por lo tanto esta funcion solo comprueba que no se usa la
-- minimizacion de Mu
esPrimitivaRecursiva :: forall n. KnownNat n => PRF n -> Bool
esPrimitivaRecursiva _f = case _f of
  {Cte _ -> True; Mas -> True; Menos -> True; Por -> True;
   Coc -> True; Res -> True; Sg -> True;
   Z -> True; S -> True; U _ -> True;
   Subst f v -> and (V.map esPrimitivaRecursiva v) && esPrimitivaRecursiva f;
   Rec f g -> esPrimitivaRecursiva f && esPrimitivaRecursiva g;
   Mu _ -> False;
  }

-- | COMPROBACIONES

-- Debe ocurrir pruebaDivision x y == x siempre que y /= 0
pruebaDivision :: Natural -> Natural -> Natural
pruebaDivision = evalPRF (Coc * U fOne + Res) . V.fromTuple ... (,)

-- | FUNCIONES para ayudar en la escritura de PRFs.

-- useArgs sustituye las variables de una funcion f n-aria por las que
-- vienen dadas por el vector v para obtener una funcion m-aria.
-- useArgs @3 @4 f(x1,x2,x3) (2,2,4) = f(y2, y2, y4)
useArgs :: forall m n. (KnownNat m, KnownNat n) => Vector m (Finite n) -> PRF m -> PRF n
useArgs v f = Subst f (V.map U v)

-- flipea argumentos
flipea :: PRF 2 -> PRF 2
flipea = useArgs $ V.fromTuple (fOne, fZero)

-- fZero, fOne, fTwo dan 0, 1 ó 2 como valor de Finite n
fZero :: (KnownNat n, 1 <= n) => Finite n
fZero = natToFinite $ Proxy @0
fOne  :: (KnownNat n, 2 <= n) => Finite n
fOne = natToFinite $ Proxy @1
fTwo :: (KnownNat n, 3 <= n) => Finite n
fTwo = natToFinite $ Proxy @2

-- head2, head3 toman un vector lo bastante grande y devuelven sus
-- primeros elementos en una tupla
head2 :: (KnownNat n, 2 <= n) => Vector n a -> (a, a)
head2 v = (v `V.index` fZero, v `V.index` fOne)
head3 :: (KnownNat n, 3 <= n) => Vector n a -> (a, a, a)
head3 v = (v `V.index` fZero, v `V.index` fOne, v `V.index` fTwo)

-- Vectores pequenos
vec1 :: a -> Vector 1 a
vec1 = V.singleton
vec2 :: a -> a -> Vector 2 a
vec2 = curry V.fromTuple
vec3 :: a -> a -> a -> Vector 3 a
vec3 x y z = V.fromTuple (x, y, z)
vec4 :: a -> a -> a -> a -> Vector 4 a
vec4 x y z w = V.fromTuple (x, y, z, w)

-- composicion con 2 argumentos: (f ... g) x y = f (g x y)
infixr 8 ...
(...) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(...) = (.) . (.)

