{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.URM.PRF
  ( -- | Modulo donde defino una forma de pasar de PRFs a URMs basada
    -- | también en el libro de Cutland

    -- Tipos para pegar programas
    Pegar(..),

    -- Deslizamientos y formas canónicas
    testFormaCanonica, deslizamiento,

    -- Conversión PRF a URM
    prfExtToProg, prfToProg,

    -- Ejemplo: se puede hacer `computaFunc examplePor [4, 6]`
    examplePor,
  )
where

import Data.PRF.Funciones as F
import Data.PRF.PRFExt
import Data.URM
import qualified Data.Vector as V
import qualified Data.Vector.Sized as Sized

-- | Tipos

-- Este tipo me permite pegar programas
newtype Pegar = Pegar {unPegar :: V.Vector Orden}
  deriving (Eq, Show, Read)

instance Semigroup Pegar where
  Pegar p <> Pegar q = Pegar (p V.++ V.map (deslizamiento (length p) 0) q)

instance Monoid Pegar where
  mempty = Pegar mempty

-- | Funciones de ayuda

-- Recorta / anade ceros a un vector hasta que tenga tamano n
resizeVec' :: Int -> V.Vector Int -> V.Vector Int
resizeVec' n = V.fromList . take n . (++ repeat 0) . V.toList

-- Desliza t unidades temporales y k espaciales una orden
deslizamiento :: Int -> Int -> Orden -> Orden
deslizamiento t k = \case
  Zero m -> Zero (m + k)
  Suc m -> Suc (m + k)
  Transfer m n -> Transfer (m + k) (n + k)
  Jump m n q -> Jump (m + k) (n + k) (q + t)

-- Comprueba si un programa esta en forma canonica
testFormaCanonica :: Prog -> Bool
testFormaCanonica p = (getMaxPos . foldMap (MaxPos . go) $ p) <= s+1
  where
    go (Jump _ _ q) = q
    go _ = 0
    s = length p

-- Modifica un programa para que trabaje con la lista de registros
-- dada como entrada y devolviendo el valor en el otro registro
-- senalado. Esto requiere de rho(p) + len(p) + 1 instrucciones
trabajaCon :: V.Vector Int -> Int -> Prog -> Prog
trabajaCon ms n p = unPegar $
  Pegar (V.imap (\i m -> if m == 0
                  then Zero (i+1)
                  else Transfer m (i+1))
         ms') <>
  Pegar p <>
  Pegar (fromList [Transfer 1 n])
  where
    ms' = resizeVec' (rho p) ms

-- | Conversión PRF a URM

-- Convierte una PRF a un programa en forma estándar
prfExtToProg ::
  forall ext n.
  (KnownNat n) =>
  (forall m. (KnownNat m) => ext m -> Prog) ->
  PRFExt ext n ->
  Prog
prfExtToProg extToProg = go where
  go :: forall m. (KnownNat m) => PRFExt ext m -> Prog
  go = \case
    Z -> fromList [Zero 1]
    S -> fromList [Suc 1]
    U k -> fromList [Transfer (fromIntegral k + 1) 1]
    Extra s -> extToProg s
    Subst (go -> p) (V.map go . Sized.fromSized -> ps') -> p'' where
      p'' = unPegar $
        Pegar (V.fromList (map (\i -> Transfer i (m+i)) [1..n])) <>
        (foldMap Pegar $ V.imap
         (\i -> trabajaCon (fromList [m+1..m+n]) (m+n+i+1)) ps') <>
        Pegar (trabajaCon (V.fromList [m+n+1..m+n+k]) 1 p)
      k = length ps'
      m = getMaxPos $
        MaxPos n <> MaxPos k <>
        MaxPos (rho p) <> foldMap (MaxPos . rho) ps'
    Rec (go -> p) (go -> p') -> p''
      where
        p'' = (unPegar $
          Pegar (p''' V.++ V.fromList [Jump (t+2) (t+1) q']) <>
          Pegar (trabajaCon
                 (V.fromList $ [m+1..m+n'] ++ [t+2, t+3])
                 (t+3)
                 p')) V.++ V.fromList [Suc (t+2), Jump 1 1 q, Transfer (t+3) 1]
        p''' = unPegar $ 
          Pegar (V.fromList (map (\i -> Transfer i (m+i)) [1..n'+1])) <>
          Pegar (trabajaCon (V.fromList [1..n']) (t+3) p)
        t = m + n'
        n' = n-1
        q = length p''' + 1
        q' = length p''
        m = getMaxPos $ (MaxPos (rho p) <> MaxPos (rho p') <> MaxPos (n'+2))
    Mu (go -> p) -> p'     
      where
        -- La minimalizacion tengo que comprobar que funciona
        p' = (unPegar $
              Pegar (V.fromList (map (\i -> Transfer i (m+i)) [1..n])) <>
              Pegar (trabajaCon (V.fromList . map (+(m+1)) . take (n+1) $ [0..])
                     1
                     p)) V.++
          V.fromList [Jump 1 (m+n+2) q, Suc (m+n+1), Jump 1 1 q', Transfer (m+n+1) 1]
        m = max (rho p) (n+1)
        q = length p'
        q' = n+1
        --n' = n+1
     where
       n = fromIntegral $ natVal (Proxy @m)
  
-- Caso particular de PRF sin extensiones
prfToProg :: forall n. (KnownNat n) => PRF n -> Prog
prfToProg = prfExtToProg (\case)
    
-- | Ejemplo

-- multiplicacion en URM
examplePor :: Prog
examplePor = prfToProg F.por
