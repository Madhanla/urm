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
module Data.PRF.Operaciones (
  -- Definicion por casos
  defcasos,

  -- Funciones logicas
  lor, land, limplies, lnot,
 
  -- Sumas, productos, ... acotados
  suma, prod, muAcot, muAcot',
  existeAcot, paratodoAcot,

  -- Comparaciones
  menor, menorOIgual, mayor, mayorOIgual,
  divide,

  -- Otras funciones de divisibilidad
  numDivs, factorial, primoNesimo,
  potencia, pxEnY,
  ) where

import Data.PRF.PRFExt
import Data.Finite (weakenN)
import Data.PRF.Funciones
import Data.Monoid (Sum(..))
import qualified Data.Vector.Sized as V
-- import Data.Functor.Plus -- Quitar una cosa de semigroups que no
-- hace falta

-- | Funciones utiles

-- Funcion util que hace que una PRF m-aria tome los primeros m
-- argumentos de una lista de n
igualaArgs :: forall ext m n. (KnownNat m, KnownNat n, m <= n) =>
  PRFExt ext m -> PRFExt ext n
igualaArgs = useArgs (V.map weakenN finites)

-- Funcion util que aplica una PRF unaria f al ultimo argumento de
-- g. No se me ocurre como hacerla mas sencilla
aplicaUltimo :: forall ext n. (KnownNat n) =>
  PRFExt ext 1 -> PRFExt ext (n+1) -> PRFExt ext (n+1)
aplicaUltimo f g = g .:. (V.map (U . weakenN) finites
                          V.++ vec1 (f .:. vec1 (
                                        U (natToFinite (Proxy @n)))))

-- | Operaciones con PRFs

-- Definición por casos; se toma un vector de (funcion, predicado),
-- donde los predicados se identifican con su función característica
defcasos ::
  forall ext n.
  (KnownNat n) =>
  [(PRFExt ext n, PRFExt ext n)] ->
  PRFExt ext n
defcasos = unNL . getSum . foldMap (\(f, p) -> Sum (NL f * NL p))

-- Algebra de decidibilidad
lnot :: forall ext n. (KnownNat n) => PRFExt ext n -> PRFExt ext n
lnot p = sgbarra .:. vec1 p
land, lor, limplies :: forall ext n. (KnownNat n) =>
  PRFExt ext n -> PRFExt ext n -> PRFExt ext n
land p q = unNL (NL p * NL q)
lor p q = sg .:. vec1 (unNL (NL p + NL q))
limplies p q = lor (lnot p) q

-- Sumatorios y productorios
-- No me funciona: prod @PRF x0 $$ vec1 1 = 0 en vez de 1
prod, suma :: forall ext n. (KnownNat n) => PRFExt ext (n+1) -> PRFExt ext (n+1)
suma f = Rec cte0
  (mas .:. vec2
   (igualaArgs f)
   (U (natToFinite (Proxy @(n+1)))))
prod f = Rec (cte 1)
  (por .:. vec2
   (igualaArgs f)
   (U (natToFinite (Proxy @(n+1)))))

-- Minimizacion acotada básica mu z < y (f(*x*, z) = 0)
muAcot :: forall ext n. (KnownNat n)
  => PRFExt ext (n+1) -> PRFExt ext (n+1)
muAcot f = suma (aplicaUltimo S (prod f))

-- Minimizacion acotada general mu z < y (p(*x*, z))
muAcot' :: forall ext n. (KnownNat n)
  => PRFExt ext (n+1) ->  PRFExt ext (n+1)
muAcot' p = muAcot (lnot p)

-- Existencial acotado Ez<y (P(*x*, z)); universal acotado
existeAcot, paratodoAcot :: forall ext n. (KnownNat n)
  => PRFExt ext (n+1) -> PRFExt ext (n+1)
existeAcot   p = sg .:. vec1 (suma p)
paratodoAcot p = prod p

menor, menorOIgual, mayor, mayorOIgual :: forall ext. PRFExt ext 2
menor = desigualdad .:. vec2 (menos .:. vec2 x1 x0) cte0
menorOIgual = aplicaUltimo S menor
mayor = sgbarra .:. vec1 menorOIgual
mayorOIgual = sgbarra .:. vec1 menor

divide :: forall ext. PRFExt ext 2
divide =
  (existeAcot (igualdad .:. vec2 x1 (por .:. vec2 x2 x0)))
  .:. (vec3 x0 x1 (S .:. vec1 x1))

numDivs :: forall ext. PRFExt ext 1
numDivs = suma (divide .:. vec2 x1 x0) .:. vec2 x0 (S .:. vec1 x0)

esPrimo :: forall ext. PRFExt ext 1
esPrimo = igualdad .:. vec2 numDivs (cte 2)

factorial :: forall ext. PRFExt ext 1
factorial = prod S

-- No funciona
primoNesimo :: forall ext. PRFExt ext 1
primoNesimo = Rec cte0 $
  muAcot' (land (mayor .:. vec2 x2 x1) (esPrimo .:. vec1 x2))
  .:. vec3 x0 x1 (mas .:. vec2 (cte 2) (factorial .:. vec1 x1))

potencia :: forall ext. PRFExt ext 2
potencia = Rec (cte 1) (por .:. vec2 x2 x0)

pxEnY :: forall ext. PRFExt ext 2
pxEnY =
  muAcot' (lnot (divide .:. vec2
         (potencia .:. vec2 (primoNesimo .:. vec1 x0) (S .:. vec1 x2))
         x1))
  .:. vec3 x0 x1 x1
