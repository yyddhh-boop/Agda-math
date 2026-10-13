{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionPrecompose where

open import Cubical.Foundations.Prelude
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayClosedParameter using (curryDay-precomposeParameter)
open import DHH.Cubical.DayHomCompositionCore

private variable ℓ : Level

-- The parameter is arbitrary here, so this lemma never has to normalize
-- the two curried arguments which construct homParameter.
abstract
  homComposition-precompose : (X A B C : CubicalSet ℓ)
    (h : CubicalNatural X (DayTensor (DayHom B C) (DayHom A B)))
    → _⋆n_ {A = X} {B = DayTensor (DayHom B C) (DayHom A B)} {C = DayHom A C}
        h (homComposition A B C)
      ≡ curryDay {C = X} {A = A} {B = C}
        (_⋆n_ {A = DayTensor X A}
          {B = DayTensor (DayTensor (DayHom B C) (DayHom A B)) A} {C = C}
          (dayMap {A = X} {A' = DayTensor (DayHom B C) (DayHom A B)} {B = A} {B' = A}
            h (cubicalId A))
          (homCompositionEvaluation A B C))
  homComposition-precompose X A B C h =
    cong (λ (k : CubicalNatural (DayTensor (DayHom B C) (DayHom A B)) (DayHom A C)) →
      _⋆n_ {A = X} {B = DayTensor (DayHom B C) (DayHom A B)} {C = DayHom A C} h k)
      (homComposition-curry A B C)
    ∙ curryDay-precomposeParameter (DayTensor (DayHom B C) (DayHom A B)) X A C
        h (homCompositionEvaluation A B C)
