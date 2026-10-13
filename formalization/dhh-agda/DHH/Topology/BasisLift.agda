{-# OPTIONS --cubical --safe #-}

module DHH.Topology.BasisLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Topology.Base
open import DHH.Topology.Basis

-- Universe lifting is defined through an explicit small basis.  It
-- does NOT resize arbitrary opens from a higher universe downwards.
liftPredicate : {ℓ : Level} (ℓ' : Level) {A : Type ℓ}
  → Predicate A → Predicate (Lift {j = ℓ'} A)
liftPredicate ℓ' U x = Lift {j = ℓ'} (fst (U (lower x))) , isOfHLevelLift 1 (snd (U (lower x)))

liftBasis : {ℓ : Level} (ℓ' : Level) {A I : Type ℓ}
  → TopologicalBasis A I
  → TopologicalBasis (Lift {j = ℓ'} A) (Lift {j = ℓ'} I)
liftBasis ℓ' B = record
  { basic = λ i → liftPredicate ℓ' (basic B (lower i))
  ; covers = λ x → PT.rec squash₁
      (λ { (i , ix) → ∣ lift i , lift ix ∣₁ }) (covers B (lower x))
  ; refine = λ i j x ix jx → PT.rec squash₁
      (λ { (k , kx , inc) → ∣ lift k , lift kx ,
        (λ y ky → lift (fst (inc (lower y) (lower ky))) ,
                  lift (snd (inc (lower y) (lower ky)))) ∣₁ })
      (refine B (lower i) (lower j) (lower x) (lower ix) (lower jx))
  }

module BasisLifting {ℓ : Level} (ℓ' : Level) {A I : Type ℓ}
  (B : TopologicalBasis A I) where
  module Original = BasisTopology B
  module Lifted = BasisTopology (liftBasis ℓ' B)

  liftedTop : isSet A → Top (ℓ-max ℓ ℓ')
  liftedTop aSet = Lifted.basisTop (isOfHLevelLift 2 aSet)

  lift-open : (U : Predicate A) → Original.LocallyBasic U
    → Lifted.LocallyBasic (liftPredicate ℓ' U)
  lift-open U u x ux = PT.rec squash₁
    (λ { (i , ix , inc) → ∣ lift i , lift ix ,
      (λ y iy → lift (inc (lower y) (lower iy))) ∣₁ }) (u (lower x) (lower ux))

liftBasisContinuous : {ℓ : Level} (ℓ' : Level) {A I B J : Type ℓ}
  (P : TopologicalBasis A I) (Q : TopologicalBasis B J)
  (aSet : isSet A) (bSet : isSet B)
  → Continuous (BasisTopology.basisTop P aSet) (BasisTopology.basisTop Q bSet)
  → Continuous (BasisLifting.liftedTop ℓ' P aSet) (BasisLifting.liftedTop ℓ' Q bSet)
carrierMap (liftBasisContinuous ℓ' P Q aSet bSet f) x = lift (carrierMap f (lower x))
continuous (liftBasisContinuous ℓ' P Q aSet bSet f) =
  BasisTopology.continuous-from-basic (liftBasis ℓ' Q) (isOfHLevelLift 2 bSet)
    (BasisLifting.liftedTop ℓ' P aSet) (λ x → lift (carrierMap f (lower x)))
    (λ i → BasisLifting.lift-open ℓ' P (preimage (carrierMap f) (basic Q (lower i)))
      (continuous f (basic Q (lower i)) (BasisTopology.basic-open Q (lower i))))

liftBasisContinuous-id : {ℓ : Level} (ℓ' : Level) {A I : Type ℓ}
  (P : TopologicalBasis A I) (aSet : isSet A)
  → liftBasisContinuous ℓ' P P aSet aSet (identityContinuous (BasisTopology.basisTop P aSet))
    ≡ identityContinuous (BasisLifting.liftedTop ℓ' P aSet)
liftBasisContinuous-id ℓ' P aSet = continuousExt (λ _ → refl)

liftBasisContinuous-compose : {ℓ : Level} (ℓ' : Level) {A I B J C K : Type ℓ}
  (P : TopologicalBasis A I) (Q : TopologicalBasis B J) (R : TopologicalBasis C K)
  (aSet : isSet A) (bSet : isSet B) (cSet : isSet C)
  (f : Continuous (BasisTopology.basisTop P aSet) (BasisTopology.basisTop Q bSet))
  (g : Continuous (BasisTopology.basisTop Q bSet) (BasisTopology.basisTop R cSet))
  → liftBasisContinuous ℓ' P R aSet cSet (composeContinuous g f)
    ≡ composeContinuous (liftBasisContinuous ℓ' Q R bSet cSet g)
        (liftBasisContinuous ℓ' P Q aSet bSet f)
liftBasisContinuous-compose ℓ' P Q R aSet bSet cSet f g = continuousExt (λ _ → refl)
