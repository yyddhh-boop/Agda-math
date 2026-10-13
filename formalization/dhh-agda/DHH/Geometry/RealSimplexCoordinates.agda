{-# OPTIONS --cubical --safe #-}
module DHH.Geometry.RealSimplexCoordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; compIso)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (CatIso; isIso)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.OrdinalCuts
open import DHH.Simplicial.CutClassification
open import DHH.Topology.Base
open import DHH.Topology.Category
open import DHH.Topology.Basis
open import DHH.Topology.BasisConstructions
open import DHH.Topology.IndexedProduct
open import DHH.Geometry.DedekindReals
open import DHH.Geometry.RealTopology
open import DHH.Geometry.RealSimplex

LargeIndex : ℕ → Type₁
LargeIndex n = Lift {j = ℓ-suc ℓ-zero} (Fin (suc (suc n)))

module CoordinateAmbient (n : ℕ) = IndexedProduct intervalBasis isSetClosedUnitInterval (LargeIndex n)

-- The first and last coordinates are fixed.  Thus the n remaining
-- real coordinates satisfy 0 ≤ u₁ ≤ ... ≤ uₙ ≤ 1.
IsOrderedSimplex : (n : ℕ) → (LargeIndex n → ClosedUnitInterval) → Type₁
IsOrderedSimplex n y =
  ((i j : LargeIndex n) → lower i ≤F lower j → fst (y i) ≤ℝ fst (y j))
  × (y (lift fzero) ≡ intervalZero)
  × (y (lift (lastFin (suc n))) ≡ intervalOne)

isPropIsOrderedSimplex : (n : ℕ) (y : LargeIndex n → ClosedUnitInterval)
  → isProp (IsOrderedSimplex n y)
isPropIsOrderedSimplex n y = isProp×
  (isPropΠ3 (λ i j _ → isProp≤ℝ (fst (y i)) (fst (y j))))
  (isProp× (isSetClosedUnitInterval _ _) (isSetClosedUnitInterval _ _))

orderedCondition : (n : ℕ) → Predicate (LargeIndex n → ClosedUnitInterval)
orderedCondition n y = IsOrderedSimplex n y , isPropIsOrderedSimplex n y

module CoordinateSubspace (n : ℕ) = BasisSubspace (CoordinateAmbient.indexedBasis n)
  (isSetΠ (λ _ → isSetClosedUnitInterval)) (orderedCondition n)

OrderedRealSimplex : ℕ → Top (ℓ-suc ℓ-zero)
OrderedRealSimplex n = CoordinateSubspace.subspaceTop n

toOrderedCoordinates : (n : ℕ) → Continuous (RealSimplex n) (OrderedRealSimplex n)
toOrderedCoordinates n = CoordinateSubspace.restrict n ambient closed
  where
  ambient : Continuous (RealSimplex n) (CoordinateAmbient.productTop n)
  ambient = composeContinuous
    {X = RealSimplex n} {Y = Ambient.productTop n} {Z = CoordinateAmbient.productTop n}
    (reindexProduct {J = LargeIndex n} {K = LargeCut n}
      intervalBasis isSetClosedUnitInterval (λ i → lift (decodeCut n (lower i))))
    (SimplexSubspace.inclusion n)

  closed : (x : Carrier (RealSimplex n)) → IsOrderedSimplex n (carrierMap ambient x)
  closed (x , mono , e0 , e1) =
    (λ i j p → mono (lift (decodeCut n (lower i))) (lift (decodeCut n (lower j)))
      (decodeCut-monotone n {i = lower i} {j = lower j} p)) ,
    (cong x (cong lift (decode-zero n)) ∙ e0) ,
    (cong x (cong lift (decode-one n)) ∙ e1)

fromOrderedCoordinates : (n : ℕ) → Continuous (OrderedRealSimplex n) (RealSimplex n)
fromOrderedCoordinates n = SimplexSubspace.restrict n ambient closed
  where
  ambient : Continuous (OrderedRealSimplex n) (Ambient.productTop n)
  ambient = composeContinuous
    {X = OrderedRealSimplex n} {Y = CoordinateAmbient.productTop n} {Z = Ambient.productTop n}
    (reindexProduct {J = LargeCut n} {K = LargeIndex n}
      intervalBasis isSetClosedUnitInterval (λ c → lift (encodeCut n (lower c))))
    (CoordinateSubspace.inclusion n)

  closed : (y : Carrier (OrderedRealSimplex n)) → IsSimplex n (carrierMap ambient y)
  closed (y , mono , e0 , e1) =
    (λ c d p → mono (lift (encodeCut n (lower c))) (lift (encodeCut n (lower d)))
      (encodeCut-monotone n {c = lower c} {d = lower d} p)) ,
    (cong y (cong lift (encode-zero n)) ∙ e0) ,
    (cong y (cong lift (encode-one n)) ∙ e1)

to-after-from : (n : ℕ)
  → composeContinuous (toOrderedCoordinates n) (fromOrderedCoordinates n)
    ≡ identityContinuous (OrderedRealSimplex n)
to-after-from n = continuousExt λ y → Σ≡Prop (isPropIsOrderedSimplex n)
  (funExt λ i → cong (fst y) (cong lift (encode-decode n (lower i))))

from-after-to : (n : ℕ)
  → composeContinuous (fromOrderedCoordinates n) (toOrderedCoordinates n)
    ≡ identityContinuous (RealSimplex n)
from-after-to n = continuousExt λ x → Σ≡Prop (isPropIsSimplex n)
  (funExt λ c → cong (fst x) (cong lift (decode-encode n (lower c))))

-- This is an actual homeomorphism of product subspaces, not only a
-- carrier bijection or a formal agreement on the simplex vertices.
simplexOrderedHomeomorphism : (n : ℕ)
  → CatIso (TopCategory (ℓ-suc ℓ-zero)) (RealSimplex n) (OrderedRealSimplex n)
fst (simplexOrderedHomeomorphism n) = toOrderedCoordinates n
isIso.inv (snd (simplexOrderedHomeomorphism n)) = fromOrderedCoordinates n
isIso.sec (snd (simplexOrderedHomeomorphism n)) = to-after-from n
isIso.ret (snd (simplexOrderedHomeomorphism n)) = from-after-to n

simplexCoordinateCarrierIso : (n : ℕ)
  → Iso (Carrier (RealSimplex n)) (Carrier (OrderedRealSimplex n))
Iso.fun (simplexCoordinateCarrierIso n) = carrierMap (toOrderedCoordinates n)
Iso.inv (simplexCoordinateCarrierIso n) = carrierMap (fromOrderedCoordinates n)
Iso.rightInv (simplexCoordinateCarrierIso n) y =
  cong (λ f → carrierMap f y) (to-after-from n)
Iso.leftInv (simplexCoordinateCarrierIso n) x =
  cong (λ f → carrierMap f x) (from-after-to n)

simplexCoordinateCarrierEquivalence : (n : ℕ)
  → Carrier (RealSimplex n) ≃ Carrier (OrderedRealSimplex n)
simplexCoordinateCarrierEquivalence n = isoToEquiv (simplexCoordinateCarrierIso n)

simplexVertex-coordinate : {n : ℕ} (i : Fin (suc n)) (k : LargeIndex n)
  → fst (carrierMap (toOrderedCoordinates n) (simplexVertex i)) k
    ≡ binaryPoint (mapIndex (decodeCut n (lower k)) i)
simplexVertex-coordinate i k = refl

-- Remove the purely universe-management lift from the coordinate labels:
-- this is literally a monotone Fin(n+2)-indexed tuple of interval values.
IsFiniteOrderedSimplex : (n : ℕ) → (Fin (suc (suc n)) → ClosedUnitInterval) → Type₁
IsFiniteOrderedSimplex n y =
  ((i j : Fin (suc (suc n))) → i ≤F j → fst (y i) ≤ℝ fst (y j))
  × (y fzero ≡ intervalZero)
  × (y (lastFin (suc n)) ≡ intervalOne)

isPropIsFiniteOrderedSimplex : (n : ℕ) (y : Fin (suc (suc n)) → ClosedUnitInterval)
  → isProp (IsFiniteOrderedSimplex n y)
isPropIsFiniteOrderedSimplex n y = isProp×
  (isPropΠ3 (λ i j _ → isProp≤ℝ (fst (y i)) (fst (y j))))
  (isProp× (isSetClosedUnitInterval _ _) (isSetClosedUnitInterval _ _))

FiniteOrderedCoordinates : ℕ → Type₁
FiniteOrderedCoordinates n = Σ (Fin (suc (suc n)) → ClosedUnitInterval) (IsFiniteOrderedSimplex n)

coordinateUnliftIso : (n : ℕ) → Iso (Carrier (OrderedRealSimplex n)) (FiniteOrderedCoordinates n)
Iso.fun (coordinateUnliftIso n) (y , mono , e0 , e1) =
  (λ i → y (lift i)) , (λ i j p → mono (lift i) (lift j) p) , e0 , e1
Iso.inv (coordinateUnliftIso n) (y , mono , e0 , e1) =
  (λ i → y (lower i)) , (λ i j p → mono (lower i) (lower j) p) , e0 , e1
Iso.rightInv (coordinateUnliftIso n) y = Σ≡Prop (isPropIsFiniteOrderedSimplex n) refl
Iso.leftInv (coordinateUnliftIso n) y = Σ≡Prop (isPropIsOrderedSimplex n) refl

simplexFiniteCoordinateIso : (n : ℕ) → Iso (Carrier (RealSimplex n)) (FiniteOrderedCoordinates n)
simplexFiniteCoordinateIso n = compIso (simplexCoordinateCarrierIso n) (coordinateUnliftIso n)

simplexFiniteCoordinateEquivalence : (n : ℕ)
  → Carrier (RealSimplex n) ≃ FiniteOrderedCoordinates n
simplexFiniteCoordinateEquivalence n = isoToEquiv (simplexFiniteCoordinateIso n)
