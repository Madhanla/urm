{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.URM
  ( -- | Modulo que implementa la Maquina de Registros Ilimitados
    -- | (URM, ver Computability de Cutland). Ejemplo de uso:
    -- | runURM exampleM    -- esto da como resultado
    -- |                    -- el primer ejemplo del manual
    -- | runURM exampleM'   -- esto da como resultado
    -- |                    -- el segundo ejemplo del manual
    -- | runURM exampleM'   -- esto da como resultado
    -- |                    -- el segundo ejemplo del manual
    -- | computaFunc exampleP [6, 2] -- el mismo programa
    -- |                             -- con otro vector
    
    -- Tipos relacionados con URMs
    Orden (..), Prog,
    Estado, Config, URM,

    -- Otros tipos
    MaxPos(..),

    -- Funciones rho
    rho', rho,

    -- Ejecutar una URM
    runURM,
    computaFunc,
    exampleP, exampleM, exampleM',

    -- Funciones que ayudan con los vectores
    fromList, repeatedly, resizeVec, modVec,
  )
where

import GHC.Natural (Natural ())
import qualified Data.Vector as V
import Data.Vector
  ( Vector (),
    fromList,
    toList,
    (!),
    (//),
  )

-- Cada registro contiene un entero
type Registro = Natural  

-- Este tipo convierte N o R0+ en un monoide con el máximo
newtype MaxPos a = MaxPos {getMaxPos :: a}
  deriving (Eq, Ord, Enum, Show, Read, Num, Real, Integral)

instance (Ord a) => Semigroup (MaxPos a) where
  (<>) = max

instance (Ord a, Num a) => Monoid (MaxPos a) where
  mempty = 0

-- El número de la instrucción siguiente es un entero pequeño
type NumInstr = Int

-- Este tipo de dato me da una orden de URM
data Orden
  = Zero Int
  | Suc Int
  | Transfer Int Int
  | Jump Int Int NumInstr
  deriving (Eq, Show, Read)

-- Un programa es un vector de órdenes
type Prog = Vector Orden

-- Una configuración es un vector (en principio infinito) de registros
type Config = Vector Registro

-- Un estado es un par (c, q) donde c es una configuración y q es un
-- número de instrucción
type Estado = (Config, NumInstr)

-- Una URM es un par (p, c) donde p es un programa y c es la
-- configuración inicial
type URM = (Prog, Config)

-- | Funciones de ayuda que trabajan con vectores

-- Modifica v[i] mediante la función f
modVec :: Int -> (a -> a) -> Vector a -> Vector a
modVec i f v = v // [(i, f (v ! i))]

-- Cambia a n el tamaño de un vector rellenándolo con ceros si es
-- necesario
resizeVec :: (Monoid a) => Int -> Vector a -> Vector a
resizeVec n = fromList . take n . (++ repeat mempty) . toList

-- Crea una lista
repeatedly :: (a -> Maybe a) -> a -> [a]
repeatedly f = go
  where
    go x =
      x : case f x of
        Just y -> go y
        Nothing -> []

-- | Funciones de URM

-- Hace actuar la orden o sobre el estado (c, q)
actua :: Orden -> Estado -> Estado
actua o (c, q) = case o of
  Zero m -> (modVec (m-1) (const 0) c, q + 1)
  Suc m -> (modVec (m-1) (+ 1) c, q + 1)
  Transfer m n -> (modVec (n-1) (const (c ! (m-1))) c, q + 1)
  Jump m n q' -> (c, if (c ! (m-1)) == (c ! (n-1)) then q' else q + 1)

-- rho p es el mayor registro usado en un programa p; se puede hacer
-- para una sola instruccion con rho'
rho' :: Orden -> Int
rho' (Zero m) = m
rho' (Suc m) = m
rho' (Transfer m n) = max m n
rho' (Jump m n _q) = max m n

rho :: Prog -> Int
rho = getMaxPos . foldMap (MaxPos . rho')

-- Lleva a cabo la computacion de una URM (p, c)
runURM :: URM -> [Estado]
runURM (p, c) = repeatedly nxt (fmap getMaxPos c', 1)
  where
    c' = resizeVec (rho p) (fmap MaxPos c)
    nxt :: Estado -> Maybe Estado
    nxt s@(_c, q) =
      if q > length p
        then Nothing
        else Just (actua (p ! (q-1)) s)

-- Realiza el computo de p con entrada xs
computaFunc :: Prog -> [Registro] -> Registro
computaFunc p xs = (V.head) . fst . last $ runURM (p, fromList xs)

-- Los dos ejemplos que aparecen en el manual
exampleP :: Prog
exampleP = fromList [Jump 1 2 6, Suc 2, Suc 3, Jump 1 2 6, Jump 1 1 2, Transfer 3 1]

exampleM :: URM
exampleM = (exampleP, fromList [9, 7])

exampleM' :: URM
exampleM' = (exampleP, fromList [2, 3])
