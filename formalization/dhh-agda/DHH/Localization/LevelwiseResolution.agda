{-# OPTIONS --cubical --safe #-}

-- Public facade for the actual levelwise localization of the free
-- comonad resolution.  Proofs live in separate checked modules so the
-- interface does not duplicate their reduction work.
module DHH.Localization.LevelwiseResolution where

open import DHH.Localization.LevelwiseCore public
open import DHH.Localization.LevelwiseLaws public
open import DHH.Localization.LevelwiseFunctor public
