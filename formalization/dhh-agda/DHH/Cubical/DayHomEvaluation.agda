{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomEvaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayClosedParameter using (curryDay-evaluation-pair-β)

private variable ℓ : Level

-- Evaluation of an actual internal-Hom cell on an independent block.
applyHom : (A B : CubicalSet ℓ) (p q : ℕ)
  → Cell (DayHom A B) p → Cell A q → Cell B (p + q)
applyHom A B p q h a = mapCells {A = DayTensor (RepresentableCube p) A} {B = B} h (p + q)
  (dayPair {A = RepresentableCube p} {B = A} p q (cubeId p) a)

abstract
  evaluationHom-β : (A B : CubicalSet ℓ) (p q : ℕ)
    (h : Cell (DayHom A B) p) (a : Cell A q)
    → mapCells {A = DayTensor (DayHom A B) A} {B = B} (dayEvaluation A B) (p + q)
        (dayPair {A = DayHom A B} {B = A} p q h a)
      ≡ applyHom A B p q h a
  evaluationHom-β A B = factorDay-β
    {A = DayHom A B} {B = A} {C = B} (dayEvaluationPairing A B)

abstract
  applyHom-curry-β : (X A B : CubicalSet ℓ)
    (F : CubicalNatural (DayTensor X A) B) (p q : ℕ)
    (x : Cell X p) (a : Cell A q)
    → applyHom A B p q (mapCells {A = X} {B = DayHom A B}
        (curryDay {C = X} {A = A} {B = B} F) p x) a
      ≡ mapCells {A = DayTensor X A} {B = B} F (p + q) (dayPair {A = X} {B = A} p q x a)
  applyHom-curry-β X A B F p q x a = curryDay-evaluation-pair-β X A B F p q x a
