{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealSimplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.OrdinalCuts
open import DHH.Topology.Base
open import DHH.Topology.Basis
open import DHH.Topology.BasisConstructions
open import DHH.Topology.IndexedProduct
open import DHH.Geometry.DedekindReals
open import DHH.Geometry.RealTopology
open import DHH.Realization.Coend

-- Ordered-coordinate presentation of a real simplex: assign an
-- interval value to each cut, monotonically, with the extreme cuts
-- fixed at 0 and 1.  There are n+2 cuts, so n free coordinates.
-- The explicit finite-chain identification is proved separately.
LargeCut : ℕ → Type₁
LargeCut n = Lift {j = ℓ-suc ℓ-zero} (Cut n)

module Ambient (n : ℕ) = IndexedProduct intervalBasis isSetClosedUnitInterval (LargeCut n)

IsSimplex : (n : ℕ) → (LargeCut n → ClosedUnitInterval) → Type₁
IsSimplex n x =
  ((c d : LargeCut n) → CutLe (lower c) (lower d) → fst (x c) ≤ℝ fst (x d))
  × (x (lift (cutZero n)) ≡ intervalZero)
  × (x (lift (cutOne n)) ≡ intervalOne)

isPropIsSimplex : (n : ℕ) (x : LargeCut n → ClosedUnitInterval) → isProp (IsSimplex n x)
isPropIsSimplex n x = isProp×
  (isPropΠ3 (λ c d _ → isProp≤ℝ (fst (x c)) (fst (x d))))
  (isProp× (isSetClosedUnitInterval _ _) (isSetClosedUnitInterval _ _))

simplexCondition : (n : ℕ) → Predicate (LargeCut n → ClosedUnitInterval)
simplexCondition n x = IsSimplex n x , isPropIsSimplex n x

module SimplexSubspace (n : ℕ) = BasisSubspace (Ambient.indexedBasis n)
  (isSetΠ (λ _ → isSetClosedUnitInterval)) (simplexCondition n)

RealSimplex : ℕ → Top (ℓ-suc ℓ-zero)
RealSimplex n = SimplexSubspace.subspaceTop n

simplexBasis : (n : ℕ) → TopologicalBasis (Carrier (RealSimplex n)) (Ambient.Conditions n)
simplexBasis n = subspaceBasis (Ambient.indexedBasis n) (simplexCondition n)

simplexMap : {m n : ℕ} → OrdinalMap m n → Continuous (RealSimplex m) (RealSimplex n)
simplexMap {m} {n} f = SimplexSubspace.restrict n {X = RealSimplex m} ambientMap closed
  where
  ambientMap : Continuous (RealSimplex m) (Ambient.productTop n)
  ambientMap = composeContinuous {X = RealSimplex m} {Y = Ambient.productTop m} {Z = Ambient.productTop n}
    (reindexProduct {J = LargeCut n} {K = LargeCut m} intervalBasis isSetClosedUnitInterval (λ c → lift (pullCut f (lower c))))
    (SimplexSubspace.inclusion m)

  closed : (x : Carrier (RealSimplex m)) → IsSimplex n (carrierMap ambientMap x)
  closed (x , mono , e0 , e1) =
    (λ c d e → mono (lift (pullCut f (lower c))) (lift (pullCut f (lower d))) (pullCut-monotone f {c = lower c} {d = lower d} e)) ,
    (cong x (cong lift (pullCut-zero f)) ∙ e0) ,
    (cong x (cong lift (pullCut-one f)) ∙ e1)

simplexMap-id : (n : ℕ) → simplexMap (ordinalId n) ≡ identityContinuous (RealSimplex n)
simplexMap-id n = continuousExt λ x → Σ≡Prop (isPropIsSimplex n)
  (funExt λ c → cong (fst x) (cong lift (pullCut-id (lower c))))

simplexMap-compose : {l m n : ℕ} (f : OrdinalMap l m) (g : OrdinalMap m n)
  → simplexMap (f ⋆o g) ≡ composeContinuous (simplexMap g) (simplexMap f)
simplexMap-compose {n = n} f g = continuousExt λ x → Σ≡Prop (isPropIsSimplex n)
  (funExt λ c → cong (fst x) (cong lift (pullCut-compose f g (lower c))))

RealSimplexDiagram : DiskDiagram Delta (ℓ-suc ℓ-zero)
disk RealSimplexDiagram = RealSimplex
diskMap RealSimplexDiagram = simplexMap
disk-id RealSimplexDiagram {a = n} = simplexMap-id n
disk-compose RealSimplexDiagram = simplexMap-compose

binaryPoint : Fin 2 → ClosedUnitInterval
binaryPoint fzero = intervalZero
binaryPoint (fsuc fzero) = intervalOne
binaryPoint (fsuc (fsuc ()))

binaryPoint-monotone : (i j : Fin 2) → i ≤F j → fst (binaryPoint i) ≤ℝ fst (binaryPoint j)
binaryPoint-monotone fzero fzero e = ≤ℝ-refl zeroReal
binaryPoint-monotone fzero (fsuc fzero) e = zero≤one
binaryPoint-monotone (fsuc fzero) fzero ()
binaryPoint-monotone (fsuc fzero) (fsuc fzero) e = ≤ℝ-refl oneReal
binaryPoint-monotone (fsuc (fsuc ())) j e
binaryPoint-monotone i (fsuc (fsuc ())) e

simplexVertex : {n : ℕ} → Fin (suc n) → Carrier (RealSimplex n)
simplexVertex i = (λ c → binaryPoint (mapIndex (lower c) i)) ,
  (λ c d e → binaryPoint-monotone (mapIndex (lower c) i) (mapIndex (lower d) i) (e i)) , refl , refl

simplexMap-vertex : {m n : ℕ} (f : OrdinalMap m n) (i : Fin (suc m))
  → carrierMap (simplexMap f) (simplexVertex i) ≡ simplexVertex (mapIndex f i)
simplexMap-vertex {n = n} f i = Σ≡Prop (isPropIsSimplex n) refl
