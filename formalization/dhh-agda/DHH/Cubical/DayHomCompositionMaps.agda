{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionMaps where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayUnitLift
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayHomEvaluation
open import DHH.Cubical.DayHomNestedEvaluation

private variable ℓ : Level

open import DHH.Cubical.DayHomCompositionCore public

abstract
  homIdentity-uncurry : (A : CubicalSet ℓ)
    → uncurryDay {C = DayUnitAt ℓ} {A = A} {B = A} (homIdentity A) ≡ dayLeftUnitAt A
  homIdentity-uncurry {ℓ} A = uncurry-curryDay
    {C = DayUnitAt ℓ} {A = A} {B = A} (dayLeftUnitAt A)

abstract
  homCompositionEvaluation-β : (A B C : CubicalSet ℓ) (p q r : ℕ)
    (h : Cell (DayHom B C) p) (k : Cell (DayHom A B) q) (a : Cell A r)
    → mapCells {A = DayTensor (DayTensor (DayHom B C) (DayHom A B)) A} {B = C}
        (homCompositionEvaluation A B C) ((p + q) + r)
        (leftTripleCell (DayHom B C) (DayHom A B) A p q r h k a)
      ≡ reindex C (cubeAssociator p q r)
        (applyHom B C p (q + r) h (applyHom A B q r k a))
  homCompositionEvaluation-β {ℓ} A B C p q r h k a =
    let
      L : CubicalSet ℓ
      L = DayTensor (DayTensor (DayHom B C) (DayHom A B)) A
      T : CubicalSet ℓ
      T = DayTensor (DayHom B C) B
      t : Cell L ((p + q) + r)
      t = leftTripleCell (DayHom B C) (DayHom A B) A p q r h k a
      u : CubicalMap ((p + q) + r) (p + (q + r))
      u = cubeAssociator p q r
      v : Cell B (q + r)
      v = mapCells {A = DayTensor (DayHom A B) A} {B = B} (dayEvaluation A B) (q + r)
        (dayPair {A = DayHom A B} {B = A} q r k a)
      w : Cell B (q + r)
      w = applyHom A B q r k a
      evalH : Cell B (q + r) → Cell C (p + (q + r))
      evalH b = mapCells {A = T} {B = C} (dayEvaluation B C) (p + (q + r))
        (dayPair {A = DayHom B C} {B = B} p (q + r) h b)

      e1 : mapCells {A = L} {B = C} (homCompositionEvaluation A B C) ((p + q) + r) t
        ≡ reindex C u (evalH v)
      e1 = cong (λ (f : CubicalNatural L C) → mapCells {A = L} {B = C} f ((p + q) + r) t)
          (homCompositionEvaluation-nested A B C)
        ∙ nestedEvaluation-β (DayHom B C) (DayHom A B) A B C
          (dayEvaluation B C) (dayEvaluation A B) p q r h k a

      e2 : reindex C u (evalH v) ≡ reindex C u (evalH w)
      e2 = cong (λ (b : Cell B (q + r)) → reindex C u (evalH b))
        (evaluationHom-β A B q r k a)

      e3 : reindex C u (evalH w)
        ≡ reindex C u (applyHom B C p (q + r) h w)
      e3 = cong (reindex C u) (evaluationHom-β B C p (q + r) h w)
    in e1 ∙ e2 ∙ e3

abstract
  homComposition-β : (A B C : CubicalSet ℓ) (p q r : ℕ)
    (h : Cell (DayHom B C) p) (k : Cell (DayHom A B) q) (a : Cell A r)
    → applyHom A C (p + q) r
        (mapCells {A = DayTensor (DayHom B C) (DayHom A B)} {B = DayHom A C}
          (homComposition A B C) (p + q)
          (dayPair {A = DayHom B C} {B = DayHom A B} p q h k)) a
      ≡ reindex C (cubeAssociator p q r)
        (applyHom B C p (q + r) h (applyHom A B q r k a))
  homComposition-β {ℓ} A B C p q r h k a =
    let
      P : CubicalSet ℓ
      P = DayTensor (DayHom B C) (DayHom A B)
      L : CubicalSet ℓ
      L = DayTensor P A
      hk : Cell P (p + q)
      hk = dayPair {A = DayHom B C} {B = DayHom A B} p q h k
      t : Cell L ((p + q) + r)
      t = leftTripleCell (DayHom B C) (DayHom A B) A p q r h k a
      e1 : applyHom A C (p + q) r
          (mapCells {A = P} {B = DayHom A C} (homComposition A B C) (p + q) hk) a
        ≡ mapCells {A = L} {B = C} (homCompositionEvaluation A B C) ((p + q) + r) t
      e1 = cong (λ (f : CubicalNatural P (DayHom A C)) →
          applyHom A C (p + q) r (mapCells {A = P} {B = DayHom A C} f (p + q) hk) a)
          (homComposition-curry A B C)
        ∙ applyHom-curry-β P A C (homCompositionEvaluation A B C) (p + q) r hk a

      e2 : mapCells {A = L} {B = C} (homCompositionEvaluation A B C) ((p + q) + r) t
        ≡ reindex C (cubeAssociator p q r) (applyHom B C p (q + r) h (applyHom A B q r k a))
      e2 = homCompositionEvaluation-β A B C p q r h k a
    in e1 ∙ e2

-- Evaluate the actual internal-Hom identity on a separate cube block.
abstract
  homIdentity-β : (A : CubicalSet ℓ) (p q : ℕ)
    (v : Cell (DayUnitAt ℓ) p) (a : Cell A q)
    → applyHom A A p q
        (mapCells {A = DayUnitAt ℓ} {B = DayHom A A} (homIdentity A) p v) a
      ≡ reindex A (lower v ⊗c cubeId q) a
  homIdentity-β {ℓ} A p q v a =
    applyHom-curry-β (DayUnitAt ℓ) A A (dayLeftUnitAt A) p q v a
    ∙ dayLeftUnitAt-β A p q v a
