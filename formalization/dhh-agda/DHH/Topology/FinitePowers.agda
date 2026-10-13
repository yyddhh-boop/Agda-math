{-# OPTIONS --cubical --safe #-}

module DHH.Topology.FinitePowers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit using (Unit*; tt*; isSetUnit*)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
open import DHH.Cubes using (Position; here; there)
open import DHH.Topology.Base
open import DHH.Topology.Basis
open import DHH.Topology.BasisConstructions

private variable ℓ : Level

PowerCarrier : Type ℓ → ℕ → Type ℓ
PowerCarrier A zero = Unit*
PowerCarrier A (suc n) = A × PowerCarrier A n

power-isSet : {A : Type ℓ} → isSet A → (n : ℕ) → isSet (PowerCarrier A n)
power-isSet aSet zero = isSetUnit*
power-isSet aSet (suc n) = isSet× aSet (power-isSet aSet n)

unitBasis : (ℓ : Level) → TopologicalBasis (Unit* {ℓ}) (Unit* {ℓ})
unitBasis ℓ = record
  { basic = λ _ → whole
  ; covers = λ _ → ∣ tt* , tt* ∣₁
  ; refine = λ _ _ _ _ _ → ∣ tt* , tt* , (λ _ _ → tt* , tt*) ∣₁
  }

powerBasis : {A I : Type ℓ} → TopologicalBasis A I → (n : ℕ)
  → TopologicalBasis (PowerCarrier A n) (PowerCarrier I n)
powerBasis {ℓ = ℓ} B zero = unitBasis ℓ
powerBasis B (suc n) = productBasis B (powerBasis B n)

module FinitePowers {A I : Type ℓ} (B : TopologicalBasis A I) (aSet : isSet A) where
  module One = BasisTopology B
  module P (n : ℕ) = BasisTopology (powerBasis B n)
  module Step (n : ℕ) = BasisProduct B (powerBasis B n) aSet (power-isSet aSet n)

  powerTop : ℕ → Top ℓ
  powerTop n = P.basisTop n (power-isSet aSet n)

  headMap : (n : ℕ) → Continuous (powerTop (suc n)) (One.basisTop aSet)
  headMap n = Step.first n

  tailMap : (n : ℕ) → Continuous (powerTop (suc n)) (powerTop n)
  tailMap n = Step.second n

  consMaps : {X : Top ℓ} (n : ℕ)
    → Continuous X (One.basisTop aSet) → Continuous X (powerTop n)
    → Continuous X (powerTop (suc n))
  consMaps n = Step.pairing n

  coordinate : {n : ℕ} → Position n → Continuous (powerTop n) (One.basisTop aSet)
  coordinate {n = suc n} here = headMap n
  coordinate {n = suc n} (there p) = composeContinuous (coordinate p) (tailMap n)

  assemble : {X : Top ℓ} (n : ℕ)
    → (Position n → Continuous X (One.basisTop aSet)) → Continuous X (powerTop n)
  assemble {X} zero f = constantContinuous X (powerTop zero) tt*
  assemble (suc n) f = consMaps n (f here) (assemble n (λ p → f (there p)))

  coordinate-assemble : {X : Top ℓ} {n : ℕ}
    (f : Position n → Continuous X (One.basisTop aSet)) (p : Position n)
    → composeContinuous (coordinate p) (assemble n f) ≡ f p
  coordinate-assemble {n = suc n} f here = continuousExt (λ _ → refl)
  coordinate-assemble {n = suc n} f (there p) =
    continuousExt λ x → cong (λ k → carrierMap k x)
      (coordinate-assemble (λ q → f (there q)) p)

  powerPointExt : {n : ℕ} {x y : PowerCarrier A n}
    → ((p : Position n) → carrierMap (coordinate p) x ≡ carrierMap (coordinate p) y)
    → x ≡ y
  powerPointExt {n = zero} p = refl
  powerPointExt {n = suc n} p i = p here i , powerPointExt (λ q → p (there q)) i

  assemble-unique : {X : Top ℓ} {n : ℕ}
    (f : Position n → Continuous X (One.basisTop aSet)) (h : Continuous X (powerTop n))
    → ((p : Position n) → composeContinuous (coordinate p) h ≡ f p)
    → h ≡ assemble n f
  assemble-unique f h e = continuousExt λ x → powerPointExt λ p →
    cong (λ k → carrierMap k x) (e p ∙ sym (coordinate-assemble f p))

  insertMap : {n : ℕ} → Position (suc n) → A
    → Continuous (powerTop n) (powerTop (suc n))
  insertMap {n = n} here a = consMaps n
    (constantContinuous (powerTop n) (One.basisTop aSet) a)
    (identityContinuous (powerTop n))
  insertMap {n = suc n} (there p) a = consMaps (suc n)
    (headMap n) (composeContinuous (insertMap p a) (tailMap n))

  deleteMap : {n : ℕ} → Position (suc n)
    → Continuous (powerTop (suc n)) (powerTop n)
  deleteMap {n = n} here = tailMap n
  deleteMap {n = suc n} (there p) = consMaps n
    (headMap (suc n)) (composeContinuous (deleteMap p) (tailMap (suc n)))

  mergeMap : {n : ℕ} → Position (suc n)
    → Continuous (BasisProduct.productTop B B aSet aSet) (One.basisTop aSet)
    → Continuous (powerTop (suc (suc n))) (powerTop (suc n))
  mergeMap {n = n} here op = consMaps n
    (composeContinuous op (BasisProduct.pairing B B aSet aSet
      (headMap (suc n)) (composeContinuous (headMap n) (tailMap (suc n)))))
    (composeContinuous (tailMap n) (tailMap (suc n)))
  mergeMap {n = suc n} (there p) op = consMaps (suc n)
    (headMap (suc (suc n))) (composeContinuous (mergeMap p op) (tailMap (suc (suc n))))

-- Map every coordinate by an actual continuous function.  The zero
-- power has one point, so this includes dimension zero without choice.
mapPower : {A I B J : Type ℓ} (P : TopologicalBasis A I) (Q : TopologicalBasis B J)
  (aSet : isSet A) (bSet : isSet B)
  → Continuous (BasisTopology.basisTop P aSet) (BasisTopology.basisTop Q bSet)
  → (n : ℕ) → Continuous (FinitePowers.powerTop P aSet n) (FinitePowers.powerTop Q bSet n)
mapPower P Q aSet bSet f n = FinitePowers.assemble Q bSet n
  (λ p → composeContinuous f (FinitePowers.coordinate P aSet p))
