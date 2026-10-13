{-# OPTIONS --cubical --safe #-}
module DHH.Localization.LevelwiseLaws where

-- Complete simplicial identities on every localized hom-set.
-- These fixed-object equations are precisely the six fields needed by
-- the mapping simplicial set; they avoid projecting record-valued paths.
-- Generic passage to equality of functors is available separately in
-- DHH.Localization.FunctorEquality.
open import DHH.Localization.RigidLevelwiseLaws public
