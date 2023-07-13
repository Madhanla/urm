module Data.URM.ZURM
  ( -- | Modulo que implementa la ZURM (como la URM pero con
    -- | registros enteros). Ejemplo de uso:
    -- | computaFunc exampleBeth [3]  -- Para comprobar el valor
    -- |                              -- de la biyeccion beth en
    -- |                              -- un punto arbitrario
    -- | computaFunc exampleBeth [-2] -- Esta definida en los
    -- |                              -- negativos
    -- | computaFunc exampleBethInverse [6] -- Comprueba que son
    -- | computaFunc exampleBethInverse [3] -- inversas
    -- |
    -- | La URM que implementé aquí está basada en el Ejercicio 3-6.3
    -- | de Compuability - Cutland

    -- Tipos de una ZURM
    Orden, Prog,
    Config, Estado,
    ZURM,

    -- Pasar de una URM normal a una ZURM
    fromNtoZURM,

    -- Computar funciones con ZURMs
    actua, runZURM,
    computaFunc,

    -- Las dos funciones que hay definidas en el manual
    exampleBeth, exampleBethInverse,
  )
where

import qualified Data.URM as N
import Data.URM
  (MaxPos(..),
   repeatedly,
   resizeVec,
   modVec,
   )

import qualified Data.Vector as V
import Data.Vector (
  Vector(), (!), fromList
  )

-- Se anade la orden Pred (predecesor) con respecto de la URM
data Orden
  = Zero Int
  | Suc Int
  | Pred Int
  | Transfer Int Int
  | Jump Int Int NumInstr
  deriving (Eq, Show, Read)

-- El número de la instrucción siguiente es un entero pequeño
type NumInstr = Int

-- Ahora cada registro contiene un entero
type Registro = Integer

-- Un programa es un vector de ordenes
type Prog = Vector Orden

-- Una configuración es un vector de registros
type Config = Vector Registro

-- Un estado es un par (c, q) donde c es una configuración y q es un
-- número de instrucción
type Estado = (Config, NumInstr)

-- Una ZURM es un par (p, c) donde p es un programa y c es la
-- configuración inicial
type ZURM = (Prog, Config)

-- Pasa de una URM normal a una ZURM
fromNtoZURM :: N.Orden -> Orden
fromNtoZURM (N.Zero n) = Zero n
fromNtoZURM (N.Suc n) = Suc n
fromNtoZURM (N.Transfer m n) = Transfer m n
fromNtoZURM (N.Jump m n q) = Jump m n q

-- Hace actuar la orden o sobre el estado (c, q)
actua :: Orden -> Estado -> Estado
actua o (c, q) = case o of
  Zero m -> (modVec (m-1) (const 0) c, q + 1)
  Suc  m -> (modVec (m-1) (+ 1) c, q + 1)
  Pred m -> (modVec (m-1) (\x -> x-1) c, q + 1)
  Transfer m n -> (modVec (n-1) (const (c ! (m-1))) c, q + 1)
  Jump m n q' -> (c, if (c ! (m-1)) == (c ! (n-1)) then q' else q + 1)

-- rho p es el mayor registro usado en un programa p; se puede hacer
-- para una sola instruccion con rho'
rho' :: Orden -> Int
rho' (Zero m) = m
rho' (Pred m) = m
rho' (Suc m) = m
rho' (Transfer m n) = max m n
rho' (Jump m n _q) = max m n

rho :: Prog -> Int
rho = getMaxPos . foldMap (MaxPos . rho')

-- Lleva a cabo la computacion de una ZURM (p, c)
runZURM :: ZURM -> [Estado]
runZURM (p, c) = repeatedly nxt (fmap getMaxPos c', 1)
  where
    c' = resizeVec (rho p) (fmap MaxPos c)
    nxt :: Estado -> Maybe Estado
    nxt s@(_c, q) =
      if q > length p
        then Nothing
        else Just (actua (p ! (q-1)) s)

-- Realiza el computo de p con entrada xs
computaFunc :: Prog -> [Registro] -> Registro
computaFunc p xs = (V.head) . fst . last $ runZURM (p, fromList xs)

-- Dos ejemplos de programas que estan en el manual:
-- computan beth : Z -> N, una biyeccion, y su inversa
exampleBeth, exampleBethInverse :: Prog
exampleBeth = fromList
  [ Transfer 1 2,
    Jump 2 3 12,
    Jump 1 3 7,
    Suc 1,
    Pred 2,
    Jump 1 1 2,
    Suc 2,
    Suc 1,
    Suc 2,
    Jump 2 3 12,
    Jump 1 1 8
  ]
exampleBethInverse = fromList
  [ Jump 1 4 9,
    Pred 1,
    Pred 3,
    Jump 1 4 8,
    Pred 1,
    Suc 2,
    Jump 1 1 1,
    Transfer 3 2,
    Transfer 2 1
  ]
