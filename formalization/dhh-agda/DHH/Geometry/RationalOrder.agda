{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RationalOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Literals
open import Cubical.Data.NatPlusOne.Base using (1+_)
open import Cubical.Data.Rationals.Base as Q using (ℚ; fromNatℚ; fromNegℚ)
import Cubical.Data.Rationals.Properties as Q
import Cubical.Data.Rationals.Order as O
import Cubical.Data.Int.Base as Z

halfQ : ℚ
halfQ = Q.[ Z.pos 1 / (1+ 1) ]

zero<one : (0 O.< 1)
zero<one = 0 , refl

negativeOne<zero : (-1 O.< 0)
negativeOne<zero = 0 , refl

half-positive : (0 O.< halfQ)
half-positive = 0 , refl

double-half : (a : ℚ) → (a Q.+ a) Q.· halfQ ≡ a
double-half a =
  cong (Q._· halfQ)
    (sym (Q.·DistL+ a 1 1 ∙ cong₂ Q._+_ (Q.·IdR a) (Q.·IdR a)))
  ∙ sym (Q.·Assoc a (1 Q.+ 1) halfQ)
  ∙ cong (a Q.·_) (Q.eq/ _ _ refl)
  ∙ Q.·IdR a

midpointQ : ℚ → ℚ → ℚ
midpointQ p q = (p Q.+ q) Q.· halfQ

midpoint-above : (p q : ℚ) → p O.< q → p O.< midpointQ p q
midpoint-above p q h = subst (O._< midpointQ p q) (double-half p)
  (O.<-·o (p Q.+ p) (p Q.+ q) halfQ half-positive (O.<-o+ p q p h))

midpoint-below : (p q : ℚ) → p O.< q → midpointQ p q O.< q
midpoint-below p q h = subst (midpointQ p q O.<_) (double-half q)
  (O.<-·o (p Q.+ q) (q Q.+ q) halfQ half-positive (O.<-+o p q q h))

rational-density : (p q : ℚ) → p O.< q
                 → Σ[ r ∈ ℚ ] (p O.< r) × (r O.< q)
rational-density p q h = midpointQ p q , midpoint-above p q h , midpoint-below p q h

rational-above : (q : ℚ) → Σ[ r ∈ ℚ ] q O.< r
rational-above q = (q Q.+ 1) ,
  subst (O._< (q Q.+ 1)) (Q.+IdR q) (O.<-o+ 0 1 q zero<one)

rational-below : (q : ℚ) → Σ[ p ∈ ℚ ] p O.< q
rational-below q = (q Q.+ -1) ,
  subst ((q Q.+ -1) O.<_) (Q.+IdR q) (O.<-o+ -1 0 q negativeOne<zero)

min-below-right : (p q : ℚ) → Q.min p q O.≤ q
min-below-right p q = subst (O._≤ q) (Q.minComm q p) (O.min≤ q p)

max-above-right : (p q : ℚ) → q O.≤ Q.max p q
max-above-right p q = subst (q O.≤_) (Q.maxComm q p) (O.≤max q p)

below-min : (r p q : ℚ) → r O.< p → r O.< q → r O.< Q.min p q
below-min r p q rp rq with p O.≟ q
... | O.lt pq = subst (r O.<_) (sym (O.≤→min p q (O.<Weaken≤ p q pq))) rp
... | O.eq pq = subst (r O.<_) (sym (O.≤→min p q (O.≡Weaken≤ p q pq))) rp
... | O.gt qp = subst (r O.<_) (sym (Q.minComm p q ∙ O.≤→min q p (O.<Weaken≤ q p qp))) rq

max-below : (p q r : ℚ) → p O.< r → q O.< r → Q.max p q O.< r
max-below p q r pr qr with p O.≟ q
... | O.lt pq = subst (O._< r) (sym (O.≤→max p q (O.<Weaken≤ p q pq))) qr
... | O.eq pq = subst (O._< r) (sym (O.≤→max p q (O.≡Weaken≤ p q pq))) qr
... | O.gt qp = subst (O._< r) (sym (Q.maxComm p q ∙ O.≤→max q p (O.<Weaken≤ q p qp))) pr
