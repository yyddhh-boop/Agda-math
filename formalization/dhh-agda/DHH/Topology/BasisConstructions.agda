{-# OPTIONS --cubical --safe #-}

module DHH.Topology.BasisConstructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Topology.Base
open import DHH.Topology.Basis

private variable ℓ : Level

productBasic : {A I B J : Type ℓ}
  → TopologicalBasis A I → TopologicalBasis B J → I × J → Predicate (A × B)
productBasic P Q ij xy =
  (fst (basic P (fst ij) (fst xy)) × fst (basic Q (snd ij) (snd xy))) ,
  isProp× (snd (basic P (fst ij) (fst xy))) (snd (basic Q (snd ij) (snd xy)))

productBasis : {A I B J : Type ℓ}
  → TopologicalBasis A I → TopologicalBasis B J
  → TopologicalBasis (A × B) (I × J)
productBasis P Q = record
  { basic = productBasic P Q
  ; covers = λ { (x , y) →
      PT.rec squash₁ (λ { (i , ix) → PT.rec squash₁
        (λ { (j , jy) → ∣ (i , j) , ix , jy ∣₁ }) (covers Q y) }) (covers P x) }
  ; refine = λ { (i , j) (i' , j') (x , y) (ix , jy) (i'x , j'y) →
      PT.rec squash₁ (λ { (k , kx , kp) → PT.rec squash₁
        (λ { (l , ly , lq) → ∣ (k , l) , (kx , ly) ,
          (λ { (a , b) (ka , lb) →
            (fst (kp a ka) , fst (lq b lb)) , (snd (kp a ka) , snd (lq b lb)) }) ∣₁ })
        (refine Q j j' y jy j'y) }) (refine P i i' x ix i'x) }
  }

module BasisProduct {A I B J : Type ℓ}
  (P : TopologicalBasis A I) (Q : TopologicalBasis B J)
  (aSet : isSet A) (bSet : isSet B) where
  module PA = BasisTopology P
  module QB = BasisTopology Q
  module PQ = BasisTopology (productBasis P Q)

  productTop : Top ℓ
  productTop = PQ.basisTop (isSet× aSet bSet)

  first : Continuous productTop (PA.basisTop aSet)
  carrierMap first = fst
  continuous first = PA.continuous-from-basic aSet productTop fst
    (λ i xy ix → PT.rec squash₁
      (λ { (j , jy) → ∣ (i , j) , (ix , jy) , (λ _ q → fst q) ∣₁ })
      (covers Q (snd xy)))

  second : Continuous productTop (QB.basisTop bSet)
  carrierMap second = snd
  continuous second = QB.continuous-from-basic bSet productTop snd
    (λ j xy jy → PT.rec squash₁
      (λ { (i , ix) → ∣ (i , j) , (ix , jy) , (λ _ q → snd q) ∣₁ })
      (covers P (fst xy)))

  pairing : {X : Top ℓ}
    → Continuous X (PA.basisTop aSet) → Continuous X (QB.basisTop bSet)
    → Continuous X productTop
  carrierMap (pairing f g) x = carrierMap f x , carrierMap g x
  continuous (pairing {X} f g) = PQ.continuous-from-basic (isSet× aSet bSet) X
    (λ x → carrierMap f x , carrierMap g x) λ { (i , j) →
      meet-open (topology X) (preimage (carrierMap f) (basic P i))
        (preimage (carrierMap g) (basic Q j))
        (continuous f (basic P i) (PA.basic-open i))
        (continuous g (basic Q j) (QB.basic-open j)) }

  pairing-first : {X : Top ℓ} (f : Continuous X (PA.basisTop aSet))
    (g : Continuous X (QB.basisTop bSet))
    → composeContinuous first (pairing f g) ≡ f
  pairing-first f g = continuousExt (λ _ → refl)

  pairing-second : {X : Top ℓ} (f : Continuous X (PA.basisTop aSet))
    (g : Continuous X (QB.basisTop bSet))
    → composeContinuous second (pairing f g) ≡ g
  pairing-second f g = continuousExt (λ _ → refl)

  pairing-unique : {X : Top ℓ} (f : Continuous X (PA.basisTop aSet))
    (g : Continuous X (QB.basisTop bSet)) (h : Continuous X productTop)
    → composeContinuous first h ≡ f → composeContinuous second h ≡ g
    → h ≡ pairing f g
  pairing-unique f g h p q = continuousExt λ x i →
    carrierMap (p i) x , carrierMap (q i) x

subspaceBasis : {A I : Type ℓ} → TopologicalBasis A I → (S : Predicate A)
  → TopologicalBasis (Σ[ x ∈ A ] fst (S x)) I
basic (subspaceBasis B S) i x = basic B i (fst x)
covers (subspaceBasis B S) x = covers B (fst x)
refine (subspaceBasis B S) i j x ix jx =
  PT.rec squash₁ (λ { (k , kx , inc) → ∣ k , kx , (λ y → inc (fst y)) ∣₁ })
    (refine B i j (fst x) ix jx)

module BasisSubspace {A I : Type ℓ} (B : TopologicalBasis A I)
  (aSet : isSet A) (S : Predicate A) where
  module BA = BasisTopology B
  module BS = BasisTopology (subspaceBasis B S)

  subspaceTop : Top ℓ
  subspaceTop = BS.basisTop (isSetΣSndProp aSet (λ x → snd (S x)))

  inclusion : Continuous subspaceTop (BA.basisTop aSet)
  carrierMap inclusion = fst
  continuous inclusion = BA.continuous-from-basic aSet subspaceTop fst BS.basic-open

  restrict : {X : Top ℓ} (f : Continuous X (BA.basisTop aSet))
    → ((x : Carrier X) → fst (S (carrierMap f x))) → Continuous X subspaceTop
  carrierMap (restrict f p) x = carrierMap f x , p x
  continuous (restrict {X} f p) = BS.continuous-from-basic
    (isSetΣSndProp aSet (λ x → snd (S x))) X
    (λ x → carrierMap f x , p x)
    (λ i → continuous f (basic B i) (BA.basic-open i))

  restrict-inclusion : {X : Top ℓ} (f : Continuous X (BA.basisTop aSet))
    (p : (x : Carrier X) → fst (S (carrierMap f x)))
    → composeContinuous inclusion (restrict f p) ≡ f
  restrict-inclusion f p = continuousExt (λ _ → refl)

  restrict-unique : {X : Top ℓ} (f : Continuous X (BA.basisTop aSet))
    (p : (x : Carrier X) → fst (S (carrierMap f x)))
    (h : Continuous X subspaceTop) → composeContinuous inclusion h ≡ f
    → h ≡ restrict f p
  restrict-unique f p h e = continuousExt λ x →
    Σ≡Prop (λ a → snd (S a)) (cong (λ k → carrierMap k x) e)
