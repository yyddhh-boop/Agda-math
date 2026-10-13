{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealTopology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Rationals.Base using (ℚ)
import Cubical.Data.Rationals.Properties as Q
import Cubical.Data.Rationals.Order as O
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Geometry.RationalOrder
open import DHH.Geometry.DedekindReals
open import DHH.Topology.Base
open import DHH.Topology.Basis
open import DHH.Topology.BasisConstructions

-- Located Dedekind cuts live in Type₁.  Lift the countable rational
-- interval basis and its membership propositions into that universe;
-- no resizing axiom or union indexed by a powerset is used.
RationalIntervalIndex : Type₁
RationalIntervalIndex = Lift (ℚ × ℚ)

rationalOpenInterval : RationalIntervalIndex → Predicate ℝ
rationalOpenInterval (lift (p , q)) x =
  Lift (fst (lowerCut x p) × fst (upperCut x q)) ,
  isOfHLevelLift 1 (isProp× (snd (lowerCut x p)) (snd (upperCut x q)))

lower-max : (x : ℝ) (p q : ℚ)
  → fst (lowerCut x p) → fst (lowerCut x q) → fst (lowerCut x (Q.max p q))
lower-max x p q lp lq with p O.≟ q
... | O.lt pq = subst (λ r → fst (lowerCut x r)) (sym (O.≤→max p q (O.<Weaken≤ p q pq))) lq
... | O.eq pq = subst (λ r → fst (lowerCut x r)) (sym (O.≤→max p q (O.≡Weaken≤ p q pq))) lq
... | O.gt qp = subst (λ r → fst (lowerCut x r))
  (sym (Q.maxComm p q ∙ O.≤→max q p (O.<Weaken≤ q p qp))) lp

upper-min : (x : ℝ) (p q : ℚ)
  → fst (upperCut x p) → fst (upperCut x q) → fst (upperCut x (Q.min p q))
upper-min x p q up uq with p O.≟ q
... | O.lt pq = subst (λ r → fst (upperCut x r)) (sym (O.≤→min p q (O.<Weaken≤ p q pq))) up
... | O.eq pq = subst (λ r → fst (upperCut x r)) (sym (O.≤→min p q (O.≡Weaken≤ p q pq))) up
... | O.gt qp = subst (λ r → fst (upperCut x r))
  (sym (Q.minComm p q ∙ O.≤→min q p (O.<Weaken≤ q p qp))) uq

realBasis : TopologicalBasis ℝ RationalIntervalIndex
basic realBasis = rationalOpenInterval
covers realBasis x = PT.rec2 squash₁
  (λ { (p , lp) (q , uq) → ∣ lift (p , q) , lift (lp , uq) ∣₁ })
  (lower-inhabited (cutLaws x)) (upper-inhabited (cutLaws x))
refine realBasis (lift (p , q)) (lift (r , s)) x (lift (lp , uq)) (lift (lr , us)) =
  ∣ lift (Q.max p r , Q.min q s) ,
    lift (lower-max x p r lp lr , upper-min x q s uq us) ,
    (λ { y (lift (lm , um)) →
      lift (lower-down-≤ y p (Q.max p r) (O.≤max p r) lm ,
            upper-up-≤ y (Q.min q s) q (O.min≤ q s) um) ,
      lift (lower-down-≤ y r (Q.max p r) (max-above-right p r) lm ,
            upper-up-≤ y (Q.min q s) s (min-below-right q s) um) }) ∣₁

module RealBasisTopology = BasisTopology realBasis
module RealProduct = BasisProduct realBasis realBasis isSetℝ isSetℝ

realLine : Top (ℓ-suc ℓ-zero)
realLine = RealBasisTopology.basisTop isSetℝ

-- The local rectangle proof exactly expresses
-- p < min(x,y) < q iff p<x and p<y and (x<q or y<q).
min-basic-open : (i : RationalIntervalIndex)
  → fst (Open (topology RealProduct.productTop)
      (preimage (λ xy → minReal (fst xy) (snd xy)) (basic realBasis i)))
min-basic-open (lift (p , q)) (x , y) (lift ((lx , ly) , uxy)) =
  PT.rec squash₁ (λ
    { (inl ux) → PT.rec squash₁
        (λ { (r , ur) → ∣ (lift (p , q) , lift (p , r)) ,
          (lift (lx , ux) , lift (ly , ur)) ,
          (λ { (a , b) (lift (la , ua) , lift (lb , ub)) → lift ((la , lb) , ∣ inl ua ∣₁) }) ∣₁ })
        (upper-inhabited (cutLaws y))
    ; (inr uy) → PT.rec squash₁
        (λ { (r , ur) → ∣ (lift (p , r) , lift (p , q)) ,
          (lift (lx , ur) , lift (ly , uy)) ,
          (λ { (a , b) (lift (la , ua) , lift (lb , ub)) → lift ((la , lb) , ∣ inr ub ∣₁) }) ∣₁ })
        (upper-inhabited (cutLaws x)) }) uxy

max-basic-open : (i : RationalIntervalIndex)
  → fst (Open (topology RealProduct.productTop)
      (preimage (λ xy → maxReal (fst xy) (snd xy)) (basic realBasis i)))
max-basic-open (lift (p , q)) (x , y) (lift (lxy , (ux , uy))) =
  PT.rec squash₁ (λ
    { (inl lx) → PT.rec squash₁
        (λ { (r , lr) → ∣ (lift (p , q) , lift (r , q)) ,
          (lift (lx , ux) , lift (lr , uy)) ,
          (λ { (a , b) (lift (la , ua) , lift (lb , ub)) → lift (∣ inl la ∣₁ , (ua , ub)) }) ∣₁ })
        (lower-inhabited (cutLaws y))
    ; (inr ly) → PT.rec squash₁
        (λ { (r , lr) → ∣ (lift (r , q) , lift (p , q)) ,
          (lift (lr , ux) , lift (ly , uy)) ,
          (λ { (a , b) (lift (la , ua) , lift (lb , ub)) → lift (∣ inr lb ∣₁ , (ua , ub)) }) ∣₁ })
        (lower-inhabited (cutLaws x)) }) lxy

minRealContinuous : Continuous RealProduct.productTop realLine
carrierMap minRealContinuous xy = minReal (fst xy) (snd xy)
continuous minRealContinuous = RealBasisTopology.continuous-from-basic
  isSetℝ RealProduct.productTop (λ xy → minReal (fst xy) (snd xy)) min-basic-open

maxRealContinuous : Continuous RealProduct.productTop realLine
carrierMap maxRealContinuous xy = maxReal (fst xy) (snd xy)
continuous maxRealContinuous = RealBasisTopology.continuous-from-basic
  isSetℝ RealProduct.productTop (λ xy → maxReal (fst xy) (snd xy)) max-basic-open

-- Restricting the rational-interval basis gives the usual subspace
-- topology on the actual closed interval.  Keeping its bounds small
-- avoids adding an unnecessary Lift to the already defined carrier.
intervalBasis : TopologicalBasis ClosedUnitInterval RationalIntervalIndex
basic intervalBasis i x = basic realBasis i (fst x)
covers intervalBasis x = covers realBasis (fst x)
refine intervalBasis i j x ix jx = PT.rec squash₁
  (λ { (k , kx , inc) → ∣ k , kx , (λ y → inc (fst y)) ∣₁ })
  (refine realBasis i j (fst x) ix jx)

module IntervalBasisTopology = BasisTopology intervalBasis
module IntervalProduct = BasisProduct intervalBasis intervalBasis
  isSetClosedUnitInterval isSetClosedUnitInterval

closedUnitInterval : Top (ℓ-suc ℓ-zero)
closedUnitInterval = IntervalBasisTopology.basisTop isSetClosedUnitInterval

intervalInclusion : Continuous closedUnitInterval realLine
carrierMap intervalInclusion = fst
continuous intervalInclusion = RealBasisTopology.continuous-from-basic
  isSetℝ closedUnitInterval fst IntervalBasisTopology.basic-open

interval-restrict : {X : Top (ℓ-suc ℓ-zero)} (f : Continuous X realLine)
  (bounds : (x : Carrier X) → (zeroReal ≤ℝ carrierMap f x) × (carrierMap f x ≤ℝ oneReal))
  → Continuous X closedUnitInterval
carrierMap (interval-restrict f bounds) x = carrierMap f x , bounds x
continuous (interval-restrict {X} f bounds) = IntervalBasisTopology.continuous-from-basic
  isSetClosedUnitInterval X (λ x → carrierMap f x , bounds x)
  (λ i → continuous f (basic realBasis i) (RealBasisTopology.basic-open i))

intervalProductInclusion : Continuous IntervalProduct.productTop RealProduct.productTop
intervalProductInclusion = RealProduct.pairing
  (composeContinuous intervalInclusion IntervalProduct.first)
  (composeContinuous intervalInclusion IntervalProduct.second)

intervalMinContinuous : Continuous IntervalProduct.productTop closedUnitInterval
intervalMinContinuous = interval-restrict
  (composeContinuous minRealContinuous intervalProductInclusion)
  (λ xy → snd (intervalMin (fst xy) (snd xy)))

intervalMaxContinuous : Continuous IntervalProduct.productTop closedUnitInterval
intervalMaxContinuous = interval-restrict
  (composeContinuous maxRealContinuous intervalProductInclusion)
  (λ xy → snd (intervalMax (fst xy) (snd xy)))
