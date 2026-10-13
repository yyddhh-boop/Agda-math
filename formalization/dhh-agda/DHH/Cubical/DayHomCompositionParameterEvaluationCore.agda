{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionParameterEvaluationCore where

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
  homParameterEvaluation : (X Y A B C : CubicalSet ℓ)
    → CubicalNatural (DayTensor X B) C
    → CubicalNatural (DayTensor Y A) B
    → CubicalNatural (DayTensor (DayTensor X Y) A) C
  homParameterEvaluation X Y A B C F G =
    _⋆n_ {A = DayTensor (DayTensor X Y) A}
      {B = DayTensor (DayTensor (DayHom B C) (DayHom A B)) A} {C = C}
      (dayMap {A = DayTensor X Y}
        {A' = DayTensor (DayHom B C) (DayHom A B)} {B = A} {B' = A}
        (homParameter X Y A B C F G) (cubicalId A))
      (homCompositionEvaluation A B C)

  homParameterEvaluation-route : (X Y A B C : CubicalSet ℓ)
    (F : CubicalNatural (DayTensor X B) C)
    (G : CubicalNatural (DayTensor Y A) B)
    → homParameterEvaluation X Y A B C F G
      ≡ _⋆n_ {A = DayTensor (DayTensor X Y) A}
          {B = DayTensor (DayTensor (DayHom B C) (DayHom A B)) A} {C = C}
          (dayMap {A = DayTensor X Y}
            {A' = DayTensor (DayHom B C) (DayHom A B)} {B = A} {B' = A}
            (homParameter X Y A B C F G) (cubicalId A))
          (homCompositionEvaluation A B C)
  homParameterEvaluation-route X Y A B C F G = refl
