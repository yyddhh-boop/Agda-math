{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomGeneratorExt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Categories.Category.Base using (Category)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayAssociatorHelpers
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayHomEvaluation

private variable ℓ : Level

abstract
  applyHom-reindexParameter : (A B : CubicalSet ℓ) {p p' : ℕ}
    (f : CubicalMap p p') (q : ℕ) (h : Cell (DayHom A B) p') (a : Cell A q)
    → applyHom A B p q (reindex (DayHom A B) f h) a
      ≡ reindex B (f ⊗c cubeId q) (applyHom A B p' q h a)
  applyHom-reindexParameter A B {p} f q h a =
    cong (applyHom A B p q (reindex (DayHom A B) f h)) (sym (reindex-id A a))
    ∙ pair-natural (dayEvaluationPairing A B) f (cubeId q) h a

  applyHom-reindexInput : (A B : CubicalSet ℓ) (p : ℕ) {q q' : ℕ}
    (g : CubicalMap q q') (h : Cell (DayHom A B) p) (a : Cell A q')
    → applyHom A B p q h (reindex A g a)
      ≡ reindex B (cubeId p ⊗c g) (applyHom A B p q' h a)
  applyHom-reindexInput A B p {q} g h a =
    cong (λ k → applyHom A B p q k (reindex A g a))
      (sym (reindex-id (DayHom A B) h))
    ∙ pair-natural (dayEvaluationPairing A B) (cubeId p) g h a

-- Checking the identity chart suffices for an entire internal-Hom cell:
-- an arbitrary chart u is obtained from that chart by naturality. This
-- proves equality of complete natural transformations, at every cube.
abstract
  homCellExt : (A B : CubicalSet ℓ) (n : ℕ) (h k : Cell (DayHom A B) n)
    → ((q : ℕ) (a : Cell A q) → applyHom A B n q h a ≡ applyHom A B n q k a)
    → h ≡ k
  homCellExt A B n h k e = dayTensorExt
    {A = RepresentableCube n} {B = A} {C = B} h k
    λ p q u a →
      let
        t = dayPair {A = RepresentableCube n} {B = A} n q (cubeId n) a
        chart : dayPair {A = RepresentableCube n} {B = A} p q u a
          ≡ reindex (DayTensor (RepresentableCube n) A) (u ⊗c cubeId q) t
        chart = cong (λ v → dayPair {A = RepresentableCube n} {B = A} p q v a)
            (sym (Category.⋆IdR CubeCategory u))
          ∙ dayPair-left {A = RepresentableCube n} {B = A} u (cubeId n) a
        routeH = cong (mapCells h (p + q)) chart ∙ natural h (u ⊗c cubeId q) t
        routeK = cong (mapCells k (p + q)) chart ∙ natural k (u ⊗c cubeId q) t
      in routeH ∙ cong (reindex B (u ⊗c cubeId q)) (e q a) ∙ sym routeK
