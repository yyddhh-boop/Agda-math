{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionParameterPairing where

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

open import DHH.Cubical.DayHomCompositionParameterCore public

abstract
  homParameter-β : (X Y A B C : CubicalSet ℓ)
    (F : CubicalNatural (DayTensor X B) C)
    (G : CubicalNatural (DayTensor Y A) B) (p q : ℕ)
    (x : Cell X p) (y : Cell Y q)
    → mapCells {A = DayTensor X Y}
        {B = DayTensor (DayHom B C) (DayHom A B)}
        (homParameter X Y A B C F G) (p + q)
        (dayPair {A = X} {B = Y} p q x y)
      ≡ dayPair {A = DayHom B C} {B = DayHom A B} p q
          (mapCells {A = X} {B = DayHom B C}
            (curryDay {C = X} {A = B} {B = C} F) p x)
          (mapCells {A = Y} {B = DayHom A B}
            (curryDay {C = Y} {A = A} {B = B} G) q y)
  homParameter-β {ℓ} X Y A B C F G p q x y =
    let
      P : CubicalSet ℓ
      P = DayTensor X Y
      Q : CubicalSet ℓ
      Q = DayTensor (DayHom B C) (DayHom A B)
      xy : Cell P (p + q)
      xy = dayPair {A = X} {B = Y} p q x y
    in cong (λ (h : CubicalNatural P Q) → mapCells {A = P} {B = Q} h (p + q) xy)
        (homParameter-map X Y A B C F G)
      ∙ dayMap-β {A = X} {A' = DayHom B C} {B = Y} {B' = DayHom A B}
          (curryDay {C = X} {A = B} {B = C} F)
          (curryDay {C = Y} {A = A} {B = B} G) p q x y

