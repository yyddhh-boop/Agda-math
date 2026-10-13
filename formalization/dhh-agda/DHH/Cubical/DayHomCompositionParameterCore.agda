{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionParameterCore where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayHomEvaluation
open import DHH.Cubical.DayHomCompositionCore
open import DHH.Cubical.DayHomCompositionMaps using (homCompositionEvaluation-β)

private variable ℓ : Level

abstract
  homParameter : (X Y A B C : CubicalSet ℓ)
    → CubicalNatural (DayTensor X B) C
    → CubicalNatural (DayTensor Y A) B
    → CubicalNatural (DayTensor X Y)
        (DayTensor (DayHom B C) (DayHom A B))
  homParameter X Y A B C F G =
    dayMap {A = X} {A' = DayHom B C} {B = Y} {B' = DayHom A B}
      (curryDay {C = X} {A = B} {B = C} F)
      (curryDay {C = Y} {A = A} {B = B} G)

  homParameter-map : (X Y A B C : CubicalSet ℓ)
    (F : CubicalNatural (DayTensor X B) C)
    (G : CubicalNatural (DayTensor Y A) B)
    → homParameter X Y A B C F G
      ≡ dayMap {A = X} {A' = DayHom B C} {B = Y} {B' = DayHom A B}
          (curryDay {C = X} {A = B} {B = C} F)
          (curryDay {C = Y} {A = A} {B = B} G)
  homParameter-map X Y A B C F G = refl

