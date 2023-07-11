{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.Rapidas.Funciones
  ( -- | Modulo con ejemplos varios de PRFs. Se emplea
    -- | la variante rapida del lenguaje, que siempre se
    -- | puede traducir mediante `toPRF' a la basica

    -- * Funciones aritmeticas
    predecesor,
    minimo,
    maximo,
    dist,
    factorial,

    -- * Funciones logicas
    sg,
    sgBar,
    y,
    o,
    defcasos,

    -- * Funciones que requieren una cota
    sumB,
    prodB,
    muB,
    forallB,
    existsB,

    -- * Ejemplo
    ejemplo,
  )
where

-- import qualified Data.Finite as F

import Data.PRF.Clases
import Data.PRF.PRFExt
import Data.PRF.Rapidas
import qualified Data.Vector.Sized as V
import System.CPUTime

predecesor :: PRFRapida 1
predecesor = Subst RapMenos (vec2 (U fZero) (RapCte 1))

sg, sgBar :: PRFRapida 1
sg = Subst RapMenos (vec2 1 (U fZero))
sgBar = negate sg

factorial :: PRFRapida 1
factorial =
  Rec
    (RapCte @0 1)
    ( Subst
        RapPor
        ( vec2
            (U fOne)
            (Subst S (vec1 $ U fZero))
        )
    )

dist :: PRFRapida 2
dist = Subst RapMas (vec2 (flipea RapMenos) RapMenos)

minimo, maximo :: PRFRapida 2
minimo = Subst RapMenos (vec2 (U fZero) RapMenos)
maximo = Subst RapMas (vec2 (U fOne) RapMenos)

-- | Funciones logicas
type Predicado = PRFRapida

y :: Predicado 2
y = RapPor

o :: Predicado 2
o = maximo

-- Definicion por casos, identificando un predicado con su funcion
-- caracteristica. Se presupone que los casos forman una particion de
-- N^n.
-- defcasos [(p1, f1), ..., (pn, fn)] $$ x =
-------------------------------------  f1 x si p1 x
-------------------------------------  ..........
-------------------------------------  fn x si pn x
defcasos :: KnownNat n => [(Predicado n, PRFRapida n)] -> PRFRapida n
defcasos = foldr (\(p, f) acc -> p * f + acc) 0

-- | Sumas y productos

-- Suma acotada usando como indice maximo el ultimo argumento, y los
-- demas como argumentos para f
sumB :: forall n. KnownNat n => PRFRapida (n + 1) -> PRFRapida (n + 1)
sumB f =
  Rec
    0
    ( Subst
        RapMas
        ( vec2
            (useArgs (V.init finites) f)
            (U nPlus1)
        ) ::
        PRFRapida (n + 2)
    )
  where
    nPlus1 = natToFinite (Proxy @(n + 1))

-- Producto acotado usando como indice maximo el predecesor del ultimo
-- argumento
prodB :: forall n. KnownNat n => PRFRapida (n + 1) -> PRFRapida (n + 1)
prodB f =
  Rec
    1
    ( Subst
        RapPor
        ( vec2
            (useArgs (V.init finites) f)
            (U nPlus1)
        ) ::
        PRFRapida (n + 2)
    )
  where
    nPlus1 = natToFinite (Proxy @(n + 1))

-- Minimalizacion acotada dada una PRF f. El ultimo argumento `y'
-- indica la cota (estrictamente) superior que se utiliza; de no
-- encontrarse un valor z < y con f(z) = 0, se devuelve y
-- Falta comprobar por que va mas lento con la optimizacion
muB :: forall n. KnownNat n => PRFRapida (n + 1) -> PRFRapida (n + 1)
muB f =
  sumB
    ( Subst
        (prodB (signum f))
        ( V.imap
            (\m -> if m < n then U else (+ 1) . U)
            (finites @(n + 1))
        )
    )
  where
    n = natToFinite (Proxy @n)

-- Para todo y existe acotados. El ultimo argumento `y' indica la cota
-- estricta que se emplea.
forallB, existsB :: forall n. KnownNat n => Predicado (n + 1) -> Predicado (n + 1)
forallB = prodB
existsB = negate . forallB . negate

lt' :: PRFRapida 2
lt' = flipea . signum $ RapMenos

-- ejemplo
ejemplo :: IO ()
ejemplo = do
  let ej = muB lt'
  -- let ej = (muB (Subst dist' (vec2 4 (U (fZero @1))))) :: PRFRapida 1
  -- let ej = (Mu (Subst dist (vec2 4 (U (fZero @1))))) :: PRFRapida 0

  putStrLn "Lenta:"
  tl <- getCPUTime
  print $ toPRF ej $$ (vec2 1 5000)
  tl' <- getCPUTime
  putStrLn $ "Tiempo: " ++ show (fromInteger (tl' - tl) / 1e12 :: Double)

  putStrLn "Rapida:"
  t <- getCPUTime
  print $ ej $$ (vec2 1 5000)
  t' <- getCPUTime
  putStrLn $ "Tiempo: " ++ show (fromInteger (t' - t) / 1e12 :: Double)
