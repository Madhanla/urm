{-# LANGUAGE PolyKinds #-}

module Data.PRF.Antiguas.FixPRF
  ( -- Un experimento
    Fix (..),
    FixPRF,
  )
where

import Data.PRF.Antiguas.PRFExt

newtype Fix f n = F (f (Fix f) n)

-- La extension del lenguaje es el propio lenguaje
type FixPRF = Fix PRFExt
