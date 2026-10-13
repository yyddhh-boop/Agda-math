{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionCore where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayUnitLift
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayHomEvaluation
open import DHH.Cubical.DayHomNestedEvaluation

private variable ℓ : Level

homIdentity : (A : CubicalSet ℓ) → CubicalNatural (DayUnitAt ℓ) (DayHom A A)
homIdentity {ℓ} A = curryDay {C = DayUnitAt ℓ} {A = A} {B = A} (dayLeftUnitAt A)

-- Keep the concrete evaluation route behind a checked equation so
-- later conversion does not unfold the two Day quotient eliminations.
abstract
  homCompositionEvaluation : (A B C : CubicalSet ℓ)
    → CubicalNatural (DayTensor (DayTensor (DayHom B C) (DayHom A B)) A) C
  homCompositionEvaluation A B C = nestedEvaluation (DayHom B C) (DayHom A B) A B C
    (dayEvaluation B C) (dayEvaluation A B)

  homCompositionEvaluation-nested : (A B C : CubicalSet ℓ)
    → homCompositionEvaluation A B C
      ≡ nestedEvaluation (DayHom B C) (DayHom A B) A B C
        (dayEvaluation B C) (dayEvaluation A B)
  homCompositionEvaluation-nested A B C = refl

abstract
  homComposition : (A B C : CubicalSet ℓ)
    → CubicalNatural (DayTensor (DayHom B C) (DayHom A B)) (DayHom A C)
  homComposition A B C = curryDay
    {C = DayTensor (DayHom B C) (DayHom A B)} {A = A} {B = C}
    (homCompositionEvaluation A B C)

  homComposition-curry : (A B C : CubicalSet ℓ)
    → homComposition A B C
      ≡ curryDay {C = DayTensor (DayHom B C) (DayHom A B)} {A = A} {B = C}
        (homCompositionEvaluation A B C)
  homComposition-curry A B C = refl
