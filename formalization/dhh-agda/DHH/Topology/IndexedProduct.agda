{-# OPTIONS --cubical --safe #-}

module DHH.Topology.IndexedProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt*)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
open import DHH.Topology.Base
open import DHH.Topology.Basis

private variable ℓ : Level

-- Finite lists of cylinder conditions are a small basis for the
-- product topology, even when the coordinate type J is infinite.
-- No choice principle or powerset-sized indexing is involved.
module IndexedProduct {A I : Type ℓ} (B : TopologicalBasis A I)
  (aSet : isSet A) (J : Type ℓ) where

  Conditions : Type ℓ
  Conditions = List (J × I)

  conditions : Conditions → Predicate (J → A)
  conditions [] f = whole f
  conditions ((j , i) ∷ rest) f =
    (fst (basic B i (f j)) × fst (conditions rest f)) ,
    isProp× (snd (basic B i (f j))) (snd (conditions rest f))

  append-conditions : (xs ys : Conditions) (f : J → A)
    → fst (conditions xs f) → fst (conditions ys f) → fst (conditions (xs ++ ys) f)
  append-conditions [] ys f px py = py
  append-conditions (ji ∷ xs) ys f (p , px) py = p , append-conditions xs ys f px py

  split-conditions : (xs ys : Conditions) (f : J → A)
    → fst (conditions (xs ++ ys) f) → fst (conditions xs f) × fst (conditions ys f)
  split-conditions [] ys f p = tt* , p
  split-conditions (ji ∷ xs) ys f (p , ps) =
    (p , fst (split-conditions xs ys f ps)) , snd (split-conditions xs ys f ps)

  indexedBasis : TopologicalBasis (J → A) Conditions
  indexedBasis = record
    { basic = conditions
    ; covers = λ _ → ∣ [] , tt* ∣₁
    ; refine = λ xs ys f px py →
        ∣ xs ++ ys , append-conditions xs ys f px py , split-conditions xs ys ∣₁
    }

  module ProductBasis = BasisTopology indexedBasis

  productTop : Top ℓ
  productTop = ProductBasis.basisTop (isSetΠ (λ _ → aSet))

  projection : (j : J) → Continuous productTop (BasisTopology.basisTop B aSet)
  carrierMap (projection j) f = f j
  continuous (projection j) = BasisTopology.continuous-from-basic B aSet productTop
    (λ f → f j) (λ i f p → ∣ (j , i) ∷ [] , (p , tt*) , (λ _ q → fst q) ∣₁)

  assemble : {X : Top ℓ} → (J → Continuous X (BasisTopology.basisTop B aSet))
    → Continuous X productTop
  carrierMap (assemble f) x j = carrierMap (f j) x
  continuous (assemble {X} f) = ProductBasis.continuous-from-basic
    (isSetΠ (λ _ → aSet)) X (λ x j → carrierMap (f j) x) cylinders-open
    where
    cylinders-open : (xs : Conditions)
      → fst (Open (topology X) (preimage (λ x j → carrierMap (f j) x) (conditions xs)))
    cylinders-open [] = whole-open (topology X)
    cylinders-open ((j , i) ∷ xs) = meet-open (topology X)
      (preimage (carrierMap (f j)) (basic B i))
      (preimage (λ x j → carrierMap (f j) x) (conditions xs))
      (continuous (f j) (basic B i) (BasisTopology.basic-open B i))
      (cylinders-open xs)

  projection-assemble : {X : Top ℓ}
    (f : J → Continuous X (BasisTopology.basisTop B aSet)) (j : J)
    → composeContinuous (projection j) (assemble f) ≡ f j
  projection-assemble f j = continuousExt (λ _ → refl)

  assemble-unique : {X : Top ℓ}
    (f : J → Continuous X (BasisTopology.basisTop B aSet)) (h : Continuous X productTop)
    → ((j : J) → composeContinuous (projection j) h ≡ f j)
    → h ≡ assemble f
  assemble-unique f h e = continuousExt (λ x → funExt λ j → cong (λ k → carrierMap k x) (e j))

reindexProduct : {A I J K : Type ℓ} (B : TopologicalBasis A I) (aSet : isSet A)
  → (J → K) → Continuous (IndexedProduct.productTop B aSet K) (IndexedProduct.productTop B aSet J)
reindexProduct B aSet u = IndexedProduct.assemble B aSet _
  (λ j → IndexedProduct.projection B aSet _ (u j))
