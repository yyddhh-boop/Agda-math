{-# OPTIONS --cubical --safe #-}

module DHH.Topology.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import DHH.Topology.Base

-- Ordinary point-set topological spaces and continuous functions.
-- Its Dwyer-Kan localization at weak homotopy equivalences will be a
-- candidate presentation of the infinity-category of spaces.
TopCategory : (ℓ : Level) → Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Category.ob (TopCategory ℓ) = Top ℓ
Category.Hom[_,_] (TopCategory ℓ) = Continuous
Category.id (TopCategory ℓ) {X} = identityContinuous X
Category._⋆_ (TopCategory ℓ) f g = composeContinuous g f
Category.⋆IdL (TopCategory ℓ) = continuous-right-id
Category.⋆IdR (TopCategory ℓ) = continuous-left-id
Category.⋆Assoc (TopCategory ℓ) f g h = continuous-assoc f g h
Category.isSetHom (TopCategory ℓ) {X} {Y} = Continuous-isSet X Y
