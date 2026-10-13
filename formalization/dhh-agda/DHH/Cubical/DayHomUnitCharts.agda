{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomUnitCharts where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; _+_)
open import Cubical.Categories.Category.Base using (Category)
open import DHH.CubeCategory
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayCoherence using (dayTriangle-chart)

-- These are equations of actual generated cube morphisms. The unit
-- parameter can be any p→0 or q→0, at an arbitrary dimension.
abstract
  homLeftUnit-chart : (p q r : ℕ) (v : CubicalMap p zero)
    → cubeAssociator p q r ⋆c (v ⊗c cubeId (q + r))
      ≡ (v ⊗c cubeId q) ⊗c cubeId r
  homLeftUnit-chart p q r v =
    cong (λ t → cubeAssociator p q r ⋆c (v ⊗c t)) (sym (tensor-id q r))
    ∙ sym (cubeAssociator-natural v (cubeId q) (cubeId r))
    ∙ Category.⋆IdR CubeCategory ((v ⊗c cubeId q) ⊗c cubeId r)

  homRightUnit-chart : (p q r : ℕ) (v : CubicalMap q zero)
    → cubeAssociator p q r ⋆c (cubeId p ⊗c (v ⊗c cubeId r))
      ≡ ((cubeId p ⊗c v) ⋆c cubeRightUnit p) ⊗c cubeId r
  homRightUnit-chart p q r v =
    let w = ((cubeId p ⊗c v) ⋆c cubeRightUnit p) ⊗c cubeId r
    in cong (cubeAssociator p q r ⋆c_) (sym (dayTriangle-chart p q r v))
      ∙ sym (Category.⋆Assoc CubeCategory (cubeAssociator p q r) (cubeAssociatorInv p q r) w)
      ∙ cong (_⋆c w) (cubeAssociator-retract p q r)
      ∙ Category.⋆IdL CubeCategory w
