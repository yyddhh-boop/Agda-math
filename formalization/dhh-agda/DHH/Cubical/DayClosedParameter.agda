{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayClosedParameter where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory using (cubeId)
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociatorHelpers using (dayTensorExt)
open import DHH.Cubical.DayClosed

private variable ℓX ℓY ℓA ℓB : Level

-- Small closed-adjunction lemmas are separated from the internal-Hom
-- composition construction, so successful checks retain their cache.
-- Evaluation after curry is proved on actual universal pairings.
abstract
  curryDay-evaluation-pair-β : (X : CubicalSet ℓX) (A : CubicalSet ℓA) (B : CubicalSet ℓB)
    (F : CubicalNatural (DayTensor X A) B) (p q : ℕ)
    (x : Cell X p) (a : Cell A q)
    → mapCells {A = DayTensor (RepresentableCube p) A} {B = B}
        (mapCells {A = X} {B = DayHom A B}
          (curryDay {C = X} {A = A} {B = B} F) p x) (p + q)
        (dayPair {A = RepresentableCube p} {B = A} p q (cubeId p) a)
      ≡ mapCells {A = DayTensor X A} {B = B} F (p + q)
        (dayPair {A = X} {B = A} p q x a)
  curryDay-evaluation-pair-β X A B F p q x a =
    sym (uncurryDay-β {C = X} {A = A} {B = B}
      (curryDay {C = X} {A = A} {B = B} F) p q x a)
    ∙ cong (λ (h : CubicalNatural (DayTensor X A) B) →
        mapCells {A = DayTensor X A} {B = B} h (p + q)
          (dayPair {A = X} {B = A} p q x a))
      (uncurry-curryDay {C = X} {A = A} {B = B} F)

-- The actual closed adjunction supplies both inverse equations.
-- This injectivity statement concerns complete natural transformations.
abstract
  uncurryDay-injective : (X : CubicalSet ℓX) (A : CubicalSet ℓA) (B : CubicalSet ℓB)
    (h k : CubicalNatural X (DayHom A B))
    → uncurryDay {C = X} {A = A} {B = B} h
      ≡ uncurryDay {C = X} {A = A} {B = B} k
    → h ≡ k
  uncurryDay-injective X A B h k e =
    sym (curry-uncurryDay {C = X} {A = A} {B = B} h)
    ∙ cong (curryDay {C = X} {A = A} {B = B}) e
    ∙ curry-uncurryDay {C = X} {A = A} {B = B} k

-- Parameter precomposition is proved by first uncurrying. On the
-- coend pairing (y,a), both maps are F(h(y),a). dayTensorExt recovers
-- the complete quotient map; no classifier or dayRightId path is used.
abstract
  curryDay-precomposeParameter : (X : CubicalSet ℓX) (Y : CubicalSet ℓY)
    (A : CubicalSet ℓA) (B : CubicalSet ℓB)
    (h : CubicalNatural Y X) (F : CubicalNatural (DayTensor X A) B)
    → _⋆n_ {A = Y} {B = X} {C = DayHom A B}
        h (curryDay {C = X} {A = A} {B = B} F)
      ≡ curryDay {C = Y} {A = A} {B = B}
        (_⋆n_ {A = DayTensor Y A} {B = DayTensor X A} {C = B}
          (dayMap {A = Y} {A' = X} {B = A} {B' = A} h (cubicalId A)) F)
  curryDay-precomposeParameter X Y A B h F =
    uncurryDay-injective Y A B leftHom rightHom
      (uncurryLeft-is-composite
      ∙ sym (uncurry-curryDay {C = Y} {A = A} {B = B} composite))
    where
    leftHom : CubicalNatural Y (DayHom A B)
    leftHom = _⋆n_ {A = Y} {B = X} {C = DayHom A B}
      h (curryDay {C = X} {A = A} {B = B} F)

    parameter : CubicalNatural (DayTensor Y A) (DayTensor X A)
    parameter = dayMap {A = Y} {A' = X} {B = A} {B' = A} h (cubicalId A)

    composite : CubicalNatural (DayTensor Y A) B
    composite = _⋆n_ {A = DayTensor Y A} {B = DayTensor X A} {C = B} parameter F

    rightHom : CubicalNatural Y (DayHom A B)
    rightHom = curryDay {C = Y} {A = A} {B = B} composite

    leftUncurried : CubicalNatural (DayTensor Y A) B
    leftUncurried = uncurryDay {C = Y} {A = A} {B = B} leftHom

    uncurryLeft-is-composite : leftUncurried ≡ composite
    uncurryLeft-is-composite = dayTensorExt {A = Y} {B = A} {C = B}
      leftUncurried composite λ p q y a →
      uncurryDay-β {C = Y} {A = A} {B = B} leftHom p q y a
      ∙ curryDay-evaluation-pair-β X A B F p q (mapCells {A = Y} {B = X} h p y) a
      ∙ sym
        (cong (mapCells {A = DayTensor X A} {B = B} F (p + q))
          (dayMap-β {A = Y} {A' = X} {B = A} {B' = A}
            h (cubicalId A) p q y a))

-- Four independent arbitrary universes, all dimensions and all set-valued
-- cubical presheaves. The proof uses only the checked closed adjunction,
-- coend extensionality, and actual β laws; no choice or Kan premise.
