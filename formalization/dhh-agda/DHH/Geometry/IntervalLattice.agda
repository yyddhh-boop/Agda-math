{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.IntervalLattice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (ℚ; fromNatℚ; fromNegℚ)
import Cubical.Data.Rationals.Order as O
import Cubical.Functions.Logic as Logic
open import Cubical.Algebra.DistLattice.Base using (DistLattice; makeDistLattice∧lOver∨l)
open import DHH.Geometry.RationalOrder
open import DHH.Geometry.DedekindReals

realCutPath : {x y : ℝ} → lowerCut x ≡ lowerCut y → upperCut x ≡ upperCut y → x ≡ y
realCutPath lp up = Σ≡Prop (λ LU → isPropIsDedekindCut (fst LU) (snd LU))
  (λ i → lp i , up i)

minReal-comm : (x y : ℝ) → minReal x y ≡ minReal y x
minReal-comm x y = realCutPath
  (funExt λ q → Logic.⊓-comm (lowerCut x q) (lowerCut y q))
  (funExt λ q → Logic.⊔-comm (upperCut x q) (upperCut y q))

maxReal-comm : (x y : ℝ) → maxReal x y ≡ maxReal y x
maxReal-comm x y = realCutPath
  (funExt λ q → Logic.⊔-comm (lowerCut x q) (lowerCut y q))
  (funExt λ q → Logic.⊓-comm (upperCut x q) (upperCut y q))

minReal-assoc : (x y z : ℝ) → minReal x (minReal y z) ≡ minReal (minReal x y) z
minReal-assoc x y z = realCutPath
  (funExt λ q → Logic.⊓-assoc (lowerCut x q) (lowerCut y q) (lowerCut z q))
  (funExt λ q → Logic.⊔-assoc (upperCut x q) (upperCut y q) (upperCut z q))

maxReal-assoc : (x y z : ℝ) → maxReal x (maxReal y z) ≡ maxReal (maxReal x y) z
maxReal-assoc x y z = realCutPath
  (funExt λ q → Logic.⊔-assoc (lowerCut x q) (lowerCut y q) (lowerCut z q))
  (funExt λ q → Logic.⊓-assoc (upperCut x q) (upperCut y q) (upperCut z q))

minReal-idem : (x : ℝ) → minReal x x ≡ x
minReal-idem x = min-of-≤ (≤ℝ-refl x)

maxReal-idem : (x : ℝ) → maxReal x x ≡ x
maxReal-idem x = max-of-≤ (≤ℝ-refl x)

minReal-absorb : (x y : ℝ) → minReal x (maxReal x y) ≡ x
minReal-absorb x y = min-of-≤ (left≤max x y)

minReal-distributes : (x y z : ℝ)
  → minReal x (maxReal y z) ≡ maxReal (minReal x y) (minReal x z)
minReal-distributes x y z = realCutPath
  (funExt λ q → Logic.⊓-⊔-distribˡ (lowerCut x q) (lowerCut y q) (lowerCut z q))
  (funExt λ q → Logic.⊔-⊓-distribˡ (upperCut x q) (upperCut y q) (upperCut z q))

intervalMin-comm : (x y : ClosedUnitInterval) → intervalMin x y ≡ intervalMin y x
intervalMin-comm x y = intervalExt (minReal-comm (fst x) (fst y))

intervalMax-comm : (x y : ClosedUnitInterval) → intervalMax x y ≡ intervalMax y x
intervalMax-comm x y = intervalExt (maxReal-comm (fst x) (fst y))

intervalMin-assoc : (x y z : ClosedUnitInterval)
  → intervalMin x (intervalMin y z) ≡ intervalMin (intervalMin x y) z
intervalMin-assoc x y z = intervalExt (minReal-assoc (fst x) (fst y) (fst z))

intervalMax-assoc : (x y z : ClosedUnitInterval)
  → intervalMax x (intervalMax y z) ≡ intervalMax (intervalMax x y) z
intervalMax-assoc x y z = intervalExt (maxReal-assoc (fst x) (fst y) (fst z))

intervalMin-idem : (x : ClosedUnitInterval) → intervalMin x x ≡ x
intervalMin-idem x = intervalExt (minReal-idem (fst x))

intervalMax-idem : (x : ClosedUnitInterval) → intervalMax x x ≡ x
intervalMax-idem x = intervalExt (maxReal-idem (fst x))

intervalMin-absorb : (x y : ClosedUnitInterval) → intervalMin x (intervalMax x y) ≡ x
intervalMin-absorb x y = intervalExt (minReal-absorb (fst x) (fst y))

intervalMin-distributes : (x y z : ClosedUnitInterval)
  → intervalMin x (intervalMax y z) ≡ intervalMax (intervalMin x y) (intervalMin x z)
intervalMin-distributes x y z = intervalExt (minReal-distributes (fst x) (fst y) (fst z))

-- An actual bounded distributive lattice on the real closed interval.
-- It can interpret cubical min/max words without assuming a decidable
-- total order on arbitrary Dedekind reals.
intervalDistLattice : DistLattice (ℓ-suc ℓ-zero)
intervalDistLattice = makeDistLattice∧lOver∨l
  intervalZero intervalOne intervalMax intervalMin isSetClosedUnitInterval
  intervalMax-assoc
  (λ x → intervalMax-comm x intervalZero ∙ interval-max-zero x)
  intervalMax-comm
  intervalMin-assoc interval-min-one intervalMin-comm
  intervalMin-absorb intervalMin-distributes

rationalReal-injective : (p q : ℚ) → rationalReal p ≡ rationalReal q → p ≡ q
rationalReal-injective p q path = O.isConnected< p q (not-pq , not-qp)
  where
  not-pq : p O.< q → ⊥
  not-pq pq = O.isIrrefl< p
    (O.isTrans< p (midpointQ p q) p (midpoint-above p q pq)
      (subst (λ x → fst (lowerCut x (midpointQ p q))) (sym path) (midpoint-below p q pq)))
  not-qp : q O.< p → ⊥
  not-qp qp = O.isIrrefl< q
    (O.isTrans< q (midpointQ q p) q (midpoint-above q p qp)
      (subst (λ x → fst (lowerCut x (midpointQ q p))) path (midpoint-below q p qp)))

zeroReal≠oneReal : zeroReal ≡ oneReal → ⊥
zeroReal≠oneReal path = O.isIrrefl< 0
  (subst (0 O.<_) (sym (rationalReal-injective 0 1 path)) zero<one)

intervalZero≠intervalOne : intervalZero ≡ intervalOne → ⊥
intervalZero≠intervalOne path = zeroReal≠oneReal (cong fst path)
