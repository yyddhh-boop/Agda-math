{-# OPTIONS --cubical --safe #-}

-- Point-set topology: carriers are sets.  Paths in a carrier express
-- equality of points, not topological paths; the latter are continuous
-- interval maps.  All unions here are indexed by types in the carrier
-- universe.  No propositional resizing is assumed.
module DHH.Topology.Base where

open import Cubical.Foundations.Prelude hiding (empty)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit.Base using (Unit*; tt*)
open import Cubical.Data.Empty.Base using (⊥*)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.SetQuotients.Base using (_/_; [_]; eq/; squash/)
import Cubical.HITs.SetQuotients.Properties as SQ
import Cubical.HITs.PropositionalTruncation.Properties as PT

private
  variable
    ℓ : Level
    A B : Type ℓ

Predicate : (A : Type ℓ) → Type (ℓ-suc ℓ)
Predicate {ℓ} A = A → hProp ℓ

whole : Predicate A
whole _ = Unit* , (λ _ _ → refl)

empty : Predicate A
empty _ = ⊥* , λ ()

infixr 30 _∩p_
_∩p_ : Predicate A → Predicate A → Predicate A
(U ∩p V) x = (fst (U x) × fst (V x)) , isProp× (snd (U x)) (snd (V x))

union : {ℓ : Level} {A : Type ℓ} → (J : Type ℓ) → (J → Predicate A) → Predicate A
union J U x = ∥ Σ[ j ∈ J ] fst (U j x) ∥₁ , squash₁

preimage : {ℓ : Level} {A B : Type ℓ} → (A → B) → Predicate B → Predicate A
preimage f U x = U (f x)

record Topology {ℓ : Level} (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Open : Predicate A → hProp ℓ
    whole-open : fst (Open whole)
    empty-open : fst (Open empty)
    meet-open : (U V : Predicate A)
              → fst (Open U) → fst (Open V) → fst (Open (U ∩p V))
    union-open : (J : Type ℓ) (U : J → Predicate A)
               → ((j : J) → fst (Open (U j))) → fst (Open (union J U))

open Topology public

record Top (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    carrier-isSet : isSet Carrier
    topology : Topology Carrier

open Top public

IsContinuous : (X Y : Top ℓ) → (Carrier X → Carrier Y) → Type (ℓ-suc ℓ)
IsContinuous X Y f = (U : Predicate (Carrier Y))
  → fst (Open (topology Y) U)
  → fst (Open (topology X) (preimage f U))

isPropIsContinuous : (X Y : Top ℓ) (f : Carrier X → Carrier Y)
                   → isProp (IsContinuous X Y f)
isPropIsContinuous X Y f = isPropΠ2 λ U _ → snd (Open (topology X) (preimage f U))

record Continuous (X Y : Top ℓ) : Type (ℓ-suc ℓ) where
  field
    carrierMap : Carrier X → Carrier Y
    continuous : IsContinuous X Y carrierMap

open Continuous public

continuousExt : {X Y : Top ℓ} {f g : Continuous X Y}
  → ((x : Carrier X) → carrierMap f x ≡ carrierMap g x) → f ≡ g
carrierMap (continuousExt p i) x = p x i
continuous (continuousExt {X = X} {Y = Y} {f = f} {g = g} p i) =
  isProp→PathP (λ i → isPropIsContinuous X Y (λ x → p x i))
    (continuous f) (continuous g) i

continuousΣIso : (X Y : Top ℓ)
  → Iso (Continuous X Y) (Σ (Carrier X → Carrier Y) (IsContinuous X Y))
Iso.fun (continuousΣIso X Y) f = carrierMap f , continuous f
carrierMap (Iso.inv (continuousΣIso X Y) (f , p)) = f
continuous (Iso.inv (continuousΣIso X Y) (f , p)) = p
Iso.rightInv (continuousΣIso X Y) _ = refl
Iso.leftInv (continuousΣIso X Y) _ = refl

Continuous-isSet : (X Y : Top ℓ) → isSet (Continuous X Y)
Continuous-isSet X Y = isOfHLevelRetractFromIso 2 (continuousΣIso X Y)
  (isSetΣSndProp (isSetΠ (λ _ → carrier-isSet Y)) (isPropIsContinuous X Y))

identityContinuous : (X : Top ℓ) → Continuous X X
carrierMap (identityContinuous X) x = x
continuous (identityContinuous X) U p = p

composeContinuous : {X Y Z : Top ℓ}
  → Continuous Y Z → Continuous X Y → Continuous X Z
carrierMap (composeContinuous g f) x = carrierMap g (carrierMap f x)
continuous (composeContinuous g f) U p =
  continuous f (preimage (carrierMap g) U) (continuous g U p)

continuous-left-id : {X Y : Top ℓ} (f : Continuous X Y)
  → composeContinuous (identityContinuous Y) f ≡ f
continuous-left-id f = continuousExt λ _ → refl

continuous-right-id : {X Y : Top ℓ} (f : Continuous X Y)
  → composeContinuous f (identityContinuous X) ≡ f
continuous-right-id f = continuousExt λ _ → refl

continuous-assoc : {X Y Z T : Top ℓ}
  (f : Continuous X Y) (g : Continuous Y Z) (h : Continuous Z T)
  → composeContinuous h (composeContinuous g f)
    ≡ composeContinuous (composeContinuous h g) f
continuous-assoc f g h = continuousExt λ _ → refl

-- The final topology of one function.  Surjectivity is not necessary
-- for this definition; quotient maps below are a particular instance.
finalTopology : (X : Top ℓ) (B : hSet ℓ)
  → (Carrier X → fst B) → Topology (fst B)
Open (finalTopology X B q) U = Open (topology X) (preimage q U)
whole-open (finalTopology X B q) = whole-open (topology X)
empty-open (finalTopology X B q) = empty-open (topology X)
meet-open (finalTopology X B q) U V p r =
  meet-open (topology X) (preimage q U) (preimage q V) p r
union-open (finalTopology X B q) J U p =
  union-open (topology X) J (λ j → preimage q (U j)) p

finalTop : (X : Top ℓ) (B : hSet ℓ)
  → (Carrier X → fst B) → Top ℓ
Carrier (finalTop X B q) = fst B
carrier-isSet (finalTop X B q) = snd B
topology (finalTop X B q) = finalTopology X B q

quotientMap : (X : Top ℓ) (B : hSet ℓ) (q : Carrier X → fst B)
  → Continuous X (finalTop X B q)
carrierMap (quotientMap X B q) = q
continuous (quotientMap X B q) U p = p

-- This is the actual universal continuity criterion of the final
-- topology, not an unproved field in a quotient specification.
final-continuous : (X Y : Top ℓ) (B : hSet ℓ) (q : Carrier X → fst B)
  (f : fst B → Carrier Y)
  → IsContinuous X Y (λ x → f (q x))
  → IsContinuous (finalTop X B q) Y f
final-continuous X Y B q f p = p

final-pullback-continuous : (X Y : Top ℓ) (B : hSet ℓ)
  (q : Carrier X → fst B) (f : fst B → Carrier Y)
  → IsContinuous (finalTop X B q) Y f
  → IsContinuous X Y (λ x → f (q x))
final-pullback-continuous X Y B q f p = p

quotientTop : (X : Top ℓ) (R : Carrier X → Carrier X → Type ℓ) → Top ℓ
quotientTop X R = finalTop X ((Carrier X / R) , squash/) [_]

setQuotientMap : (X : Top ℓ) (R : Carrier X → Carrier X → Type ℓ)
  → Continuous X (quotientTop X R)
setQuotientMap X R = quotientMap X ((Carrier X / R) , squash/) [_]

quotientFactor : {X Y : Top ℓ} (R : Carrier X → Carrier X → Type ℓ)
  (f : Continuous X Y)
  → ((a b : Carrier X) → R a b → carrierMap f a ≡ carrierMap f b)
  → Continuous (quotientTop X R) Y
carrierMap (quotientFactor {Y = Y} R f respects) =
  SQ.rec (carrier-isSet Y) (carrierMap f) respects
continuous (quotientFactor R f respects) U p = continuous f U p

quotientFactor-commutes : {X Y : Top ℓ} (R : Carrier X → Carrier X → Type ℓ)
  (f : Continuous X Y)
  (respects : (a b : Carrier X) → R a b → carrierMap f a ≡ carrierMap f b)
  → composeContinuous (quotientFactor R f respects) (setQuotientMap X R) ≡ f
quotientFactor-commutes R f respects = continuousExt λ _ → refl

quotientFactor-unique : {X Y : Top ℓ} (R : Carrier X → Carrier X → Type ℓ)
  (f : Continuous X Y)
  (respects : (a b : Carrier X) → R a b → carrierMap f a ≡ carrierMap f b)
  (g : Continuous (quotientTop X R) Y)
  → composeContinuous g (setQuotientMap X R) ≡ f
  → g ≡ quotientFactor R f respects
quotientFactor-unique {Y = Y} R f respects g p = continuousExt
  (SQ.elimProp (λ _ → carrier-isSet Y _ _) (λ a → cong (λ h → carrierMap h a) p))

-- Every constant predicate is open: it is a small union of copies of
-- the whole space.  This proof does not use excluded middle.
constant-predicate-open : (X : Top ℓ) (P : hProp ℓ)
  → fst (Open (topology X) (λ _ → P))
constant-predicate-open X P =
  subst (λ U → fst (Open (topology X) U)) comparison
    (union-open (topology X) (fst P) (λ _ → whole)
      (λ _ → whole-open (topology X)))
  where
  comparison : union (fst P) (λ _ → whole) ≡ (λ (_ : Carrier X) → P)
  comparison = funExt λ x → TypeOfHLevel≡ 1
    (hPropExt squash₁ (snd P)
      (PT.rec (snd P) fst) (λ p → ∣ p , tt* ∣₁))

constantContinuous : (X Y : Top ℓ) → Carrier Y → Continuous X Y
carrierMap (constantContinuous X Y y) _ = y
continuous (constantContinuous X Y y) U _ = constant-predicate-open X (U y)

-- The discrete topology is useful for finite shape indexing.  A real
-- interval will have its usual topology, rather than this one.
discreteTopology : (A : Type ℓ) → Topology A
Open (discreteTopology A) _ = Unit* , (λ _ _ → refl)
whole-open (discreteTopology A) = tt*
empty-open (discreteTopology A) = tt*
meet-open (discreteTopology A) _ _ _ _ = tt*
union-open (discreteTopology A) _ _ _ = tt*

discreteTop : (A : hSet ℓ) → Top ℓ
Carrier (discreteTop A) = fst A
carrier-isSet (discreteTop A) = snd A
topology (discreteTop A) = discreteTopology (fst A)

fromDiscrete : (A : hSet ℓ) (Y : Top ℓ)
  → (fst A → Carrier Y) → Continuous (discreteTop A) Y
carrierMap (fromDiscrete A Y f) = f
continuous (fromDiscrete A Y f) _ _ = tt*
