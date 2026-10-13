{-# OPTIONS --cubical --safe #-}

module DHH.Topology.Basis where

open import Cubical.Foundations.Prelude hiding (empty)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt*)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Topology.Base

private variable ℓ : Level

infix 20 _⊆p_
_⊆p_ : {A : Type ℓ} → Predicate A → Predicate A → Type ℓ
U ⊆p V = ∀ x → fst (U x) → fst (V x)

-- The basis INDEX is small.  We never take a union indexed by all
-- predicates or assume propositional resizing.  Standard real opens
-- will use rational intervals as this index.
record TopologicalBasis (A I : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    basic : I → Predicate A
    covers : (x : A) → ∥ Σ[ i ∈ I ] fst (basic i x) ∥₁
    refine : (i j : I) (x : A)
      → fst (basic i x) → fst (basic j x)
      → ∥ Σ[ k ∈ I ] (fst (basic k x) × (basic k ⊆p (basic i ∩p basic j))) ∥₁
open TopologicalBasis public

module BasisTopology {A I : Type ℓ} (B : TopologicalBasis A I) where
  LocallyBasic : Predicate A → Type ℓ
  LocallyBasic U = (x : A) → fst (U x)
    → ∥ Σ[ i ∈ I ] (fst (basic B i x) × (basic B i ⊆p U)) ∥₁

  locallyBasic-isProp : (U : Predicate A) → isProp (LocallyBasic U)
  locallyBasic-isProp U = isPropΠ2 (λ _ _ → squash₁)

  basisTopology : Topology A
  Open basisTopology U = LocallyBasic U , locallyBasic-isProp U
  whole-open basisTopology x _ = PT.rec squash₁
    (λ { (i , ix) → ∣ i , ix , (λ _ _ → tt*) ∣₁ }) (covers B x)
  empty-open basisTopology x p = Empty.rec (lower p)
  meet-open basisTopology U V u v x (ux , vx) =
    PT.rec squash₁ (λ { (i , ix , iu) →
    PT.rec squash₁ (λ { (j , jx , jv) →
    PT.rec squash₁ (λ { (k , kx , kij) →
      ∣ k , kx , (λ y ky → iu y (fst (kij y ky)) , jv y (snd (kij y ky))) ∣₁ })
      (refine B i j x ix jx) }) (v x vx) }) (u x ux)
  union-open basisTopology J U u x = PT.rec squash₁ λ { (j , ux) →
    PT.rec squash₁ (λ { (i , ix , iu) →
      ∣ i , ix , (λ y iy → ∣ j , iu y iy ∣₁) ∣₁ }) (u j x ux) }

  basic-open : (i : I) → LocallyBasic (basic B i)
  basic-open i x ix = ∣ i , ix , (λ _ p → p) ∣₁

  -- Every open is a SMALL union of basis opens contained in it.
  -- The containment proofs live in the same universe as A and I.
  open-as-union : (U : Predicate A) → LocallyBasic U
    → U ≡ union (Σ[ i ∈ I ] (basic B i ⊆p U)) (λ j → basic B (fst j))
  open-as-union U u = funExt λ x → TypeOfHLevel≡ 1
    (hPropExt (snd (U x)) squash₁
      (λ ux → PT.rec squash₁
        (λ { (i , ix , iu) → ∣ (i , iu) , ix ∣₁ }) (u x ux))
      (PT.rec (snd (U x)) (λ { ((i , iu) , ix) → iu x ix })))

  basisTop : isSet A → Top ℓ
  Carrier (basisTop aSet) = A
  carrier-isSet (basisTop aSet) = aSet
  topology (basisTop aSet) = basisTopology

  continuous-from-basic : (aSet : isSet A) (X : Top ℓ) (f : Carrier X → A)
    → ((i : I) → fst (Open (topology X) (preimage f (basic B i))))
    → IsContinuous X (basisTop aSet) f
  continuous-from-basic aSet X f p U u =
    subst (λ V → fst (Open (topology X) (preimage f V)))
      (sym (open-as-union U u))
      (union-open (topology X) (Σ[ i ∈ I ] (basic B i ⊆p U))
        (λ j → preimage f (basic B (fst j))) (λ j → p (fst j)))

  continuous-on-basic : (aSet : isSet A) (X : Top ℓ) (f : Carrier X → A)
    → IsContinuous X (basisTop aSet) f
    → (i : I) → fst (Open (topology X) (preimage f (basic B i)))
  continuous-on-basic aSet X f p i = p (basic B i) (basic-open i)
