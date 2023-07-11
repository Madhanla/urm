{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.PRF.Antiguas.Utils (
  -- | Modulo que exporta funciones y tipos utiles.
  
  -- PRFs independientes de la extension
  ident, cte0,

  -- Funciones para ayudar en la escritura de PRFs
  useArgs, flipea,
  fZero, fOne, fTwo,
  head2, head3,
  vec1, vec2, vec3, vec4,
  (...),

  -- Otras
  extend, fromBasica, embed, bind,
  ) where

import Data.PRF.Antiguas.PRFExt
import qualified Data.Vector.Sized as V

-- | PRFs sencillas independientes de la extension
-- Función identidad
ident :: forall ext. PRFExt ext 1
ident = U fZero

-- cte 0 n-aria
cte0 :: forall n ext. KnownNat n => PRFExt ext n
cte0 = useArgs V.empty Z


-- | FUNCIONES para ayudar en la escritura de PRFs.

-- useArgs sustituye las variables de una funcion f n-aria por las que
-- vienen dadas por el vector v para obtener una funcion m-aria.
-- useArgs @3 @4 f(x1,x2,x3) (2,2,4) = f(y2, y2, y4)
useArgs :: forall m n ext. (KnownNat m, KnownNat n)
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

-- Composicion con 2 argumentos: (f ... g) x y = f (g x y)
infixr 8 ...
(...) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(...) = (.) . (.)

-- | Otras cosas
-- class Embeds (ext1 :: Nat -> Type) (ext2 :: Nat -> Type) where
--   embed :: forall m. KnownNat m => ext1 m -> ext2 m
-- 
-- instance Embeds ext (PRFExt ext) where
--   embed = Extra
-- instance (Embeds ext1 ext2, Embeds ext2 ext3) =>
--   Embeds ext1 ext3 where
--   embed = embed @ext2 @ext3 . embed @ext1 @ext2

embed :: forall ext n. KnownNat n => ext n -> PRFExt ext n
embed = Extra
  
-- extend se puede implementar a partir de bind y embed. Vease
-- Data.PRF.Antiguas.Pruebas
extend :: forall ext1 ext2 n. KnownNat n =>
  (forall m. KnownNat m => ext1 m -> ext2 m) ->
  PRFExt ext1 n -> PRFExt ext2 n
extend phi = \case {Z -> Z; S -> S; U k -> U k;
                    Subst f hs -> Subst (extend phi f) (V.map (extend phi) hs);
                    Rec f g -> Rec (extend phi f) (extend phi g);
                    Mu f -> Mu (extend phi f);
                    Extra f -> Extra (phi f)}

fromBasica :: forall ext n. KnownNat n => PRF n -> PRFExt ext n
fromBasica = extend (\case)

bind :: forall ext1 ext2 m. KnownNat m =>
  (forall n. KnownNat n => ext1 n -> PRFExt ext2 n) ->
  PRFExt ext1 m -> PRFExt ext2 m
bind phi = \case {Z -> Z; S -> S; U k -> U k;
                Subst f hs -> Subst (bind phi f) (V.map (bind phi) hs);
                Rec f g -> Rec (bind phi f) (bind phi g);
                Mu f -> Mu (bind phi f);
                Extra f -> phi f}
