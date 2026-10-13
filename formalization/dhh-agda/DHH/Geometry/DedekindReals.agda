{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.DedekindReals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (ℚ; fromNatℚ; fromNegℚ)
import Cubical.Data.Rationals.Properties as Q
import Cubical.Data.Rationals.Order as O
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Geometry.RationalOrder

-- The standard constructive Dedekind real: an inhabited, rounded,
-- separated and located pair of rational cuts.  This is a definition
-- of points, not an interface asking a caller to supply a real line.
record IsDedekindCut (L U : ℚ → hProp ℓ-zero) : Type₀ where
  field
    lower-inhabited : ∥ Σ[ p ∈ ℚ ] fst (L p) ∥₁
    upper-inhabited : ∥ Σ[ q ∈ ℚ ] fst (U q) ∥₁
    lower-rounded : (p : ℚ) → fst (L p)
                  → ∥ Σ[ q ∈ ℚ ] (p O.< q) × fst (L q) ∥₁
    upper-rounded : (q : ℚ) → fst (U q)
                  → ∥ Σ[ p ∈ ℚ ] fst (U p) × (p O.< q) ∥₁
    lower-down : (p q : ℚ) → p O.< q → fst (L q) → fst (L p)
    upper-up : (p q : ℚ) → p O.< q → fst (U p) → fst (U q)
    separated : (p q : ℚ) → fst (L p) → fst (U q) → p O.< q
    located : (p q : ℚ) → p O.< q → ∥ fst (L p) ⊎ fst (U q) ∥₁
open IsDedekindCut public

isPropIsDedekindCut : (L U : ℚ → hProp ℓ-zero) → isProp (IsDedekindCut L U)
lower-inhabited (isPropIsDedekindCut L U c d i) =
  squash₁ (lower-inhabited c) (lower-inhabited d) i
upper-inhabited (isPropIsDedekindCut L U c d i) =
  squash₁ (upper-inhabited c) (upper-inhabited d) i
lower-rounded (isPropIsDedekindCut L U c d i) p h =
  squash₁ (lower-rounded c p h) (lower-rounded d p h) i
upper-rounded (isPropIsDedekindCut L U c d i) q h =
  squash₁ (upper-rounded c q h) (upper-rounded d q h) i
lower-down (isPropIsDedekindCut L U c d i) p q pq h =
  snd (L p) (lower-down c p q pq h) (lower-down d p q pq h) i
upper-up (isPropIsDedekindCut L U c d i) p q pq h =
  snd (U q) (upper-up c p q pq h) (upper-up d p q pq h) i
separated (isPropIsDedekindCut L U c d i) p q lp uq =
  O.isProp< p q (separated c p q lp uq) (separated d p q lp uq) i
located (isPropIsDedekindCut L U c d i) p q pq =
  squash₁ (located c p q pq) (located d p q pq) i

ℝ : Type₁
ℝ = Σ[ LU ∈ ((ℚ → hProp ℓ-zero) × (ℚ → hProp ℓ-zero)) ]
  IsDedekindCut (fst LU) (snd LU)

lowerCut upperCut : ℝ → ℚ → hProp ℓ-zero
lowerCut x = fst (fst x)
upperCut x = snd (fst x)

cutLaws : (x : ℝ) → IsDedekindCut (lowerCut x) (upperCut x)
cutLaws = snd

isSetℝ : isSet ℝ
isSetℝ = isSetΣSndProp
  (isSet× (isSetΠ (λ _ → isSetHProp)) (isSetΠ (λ _ → isSetHProp)))
  (λ LU → isPropIsDedekindCut (fst LU) (snd LU))

realExt : {x y : ℝ}
        → ((q : ℚ) → fst (lowerCut x q) → fst (lowerCut y q))
        → ((q : ℚ) → fst (lowerCut y q) → fst (lowerCut x q))
        → ((q : ℚ) → fst (upperCut x q) → fst (upperCut y q))
        → ((q : ℚ) → fst (upperCut y q) → fst (upperCut x q))
        → x ≡ y
realExt {x} {y} lf lb uf ub =
  Σ≡Prop (λ LU → isPropIsDedekindCut (fst LU) (snd LU))
    (λ i →
      (λ q → TypeOfHLevel≡ 1 {X = lowerCut x q} {Y = lowerCut y q}
        (hPropExt (snd (lowerCut x q)) (snd (lowerCut y q)) (lf q) (lb q)) i) ,
      (λ q → TypeOfHLevel≡ 1 {X = upperCut x q} {Y = upperCut y q}
        (hPropExt (snd (upperCut x q)) (snd (upperCut y q)) (uf q) (ub q)) i))

-- A located rounded upper cut is determined by the lower cut.
-- This is useful for proving equality by rational lower thresholds.
upper-from-lower : {x y : ℝ}
  → ((p : ℚ) → fst (lowerCut y p) → fst (lowerCut x p))
  → (q : ℚ) → fst (upperCut x q) → fst (upperCut y q)
upper-from-lower {x} {y} lyx q uxq = PT.rec (snd (upperCut y q))
  (λ { (p , uxp , pq) → PT.rec (snd (upperCut y q))
    (λ { (inl lyp) → Empty.rec (O.isIrrefl< p (separated (cutLaws x) p p (lyx p lyp) uxp))
       ; (inr uyq) → uyq })
    (located (cutLaws y) p q pq) })
  (upper-rounded (cutLaws x) q uxq)

realLowerExt : {x y : ℝ}
  → ((p : ℚ) → fst (lowerCut x p) → fst (lowerCut y p))
  → ((p : ℚ) → fst (lowerCut y p) → fst (lowerCut x p)) → x ≡ y
realLowerExt {x} {y} lxy lyx = realExt lxy lyx
  (upper-from-lower {x = x} {y = y} lyx)
  (upper-from-lower {x = y} {y = x} lxy)

rationalCut : (r : ℚ) → IsDedekindCut
  (λ p → (p O.< r) , O.isProp< p r)
  (λ q → (r O.< q) , O.isProp< r q)
lower-inhabited (rationalCut r) = ∣ rational-below r ∣₁
upper-inhabited (rationalCut r) = ∣ rational-above r ∣₁
lower-rounded (rationalCut r) p pr = ∣ rational-density p r pr ∣₁
upper-rounded (rationalCut r) q rq = ∣ rational-density r q rq ∣₁
lower-down (rationalCut r) p q pq qr = O.isTrans< p q r pq qr
upper-up (rationalCut r) p q pq rp = O.isTrans< r p q rp pq
separated (rationalCut r) p q pr rq = O.isTrans< p r q pr rq
located (rationalCut r) p q pq = O.isWeaklyLinear< p q r pq

rationalReal : ℚ → ℝ
rationalReal r =
  ((λ p → (p O.< r) , O.isProp< p r) , (λ q → (r O.< q) , O.isProp< r q)) , rationalCut r

zeroReal oneReal : ℝ
zeroReal = rationalReal 0
oneReal = rationalReal 1

lower-down-≤ : (x : ℝ) (p q : ℚ) → p O.≤ q → fst (lowerCut x q) → fst (lowerCut x p)
lower-down-≤ x p q pq lq = PT.rec (snd (lowerCut x p))
  (λ { (r , qr , lr) → lower-down (cutLaws x) p r (O.isTrans≤< p q r pq qr) lr })
  (lower-rounded (cutLaws x) q lq)

upper-up-≤ : (x : ℝ) (p q : ℚ) → p O.≤ q → fst (upperCut x p) → fst (upperCut x q)
upper-up-≤ x p q pq up = PT.rec (snd (upperCut x q))
  (λ { (r , ur , rp) → upper-up (cutLaws x) r q (O.isTrans<≤ r p q rp pq) ur })
  (upper-rounded (cutLaws x) p up)

meetProp joinProp : hProp ℓ-zero → hProp ℓ-zero → hProp ℓ-zero
meetProp P Q = (fst P × fst Q) , isProp× (snd P) (snd Q)
joinProp P Q = ∥ fst P ⊎ fst Q ∥₁ , squash₁

minLower maxUpper : ℝ → ℝ → ℚ → hProp ℓ-zero
minLower x y p = meetProp (lowerCut x p) (lowerCut y p)
maxUpper x y q = meetProp (upperCut x q) (upperCut y q)

minUpper maxLower : ℝ → ℝ → ℚ → hProp ℓ-zero
minUpper x y q = joinProp (upperCut x q) (upperCut y q)
maxLower x y p = joinProp (lowerCut x p) (lowerCut y p)

minCut : (x y : ℝ) → IsDedekindCut (minLower x y) (minUpper x y)
lower-inhabited (minCut x y) = PT.rec2 squash₁
  (λ { (p , lp) (q , lq) → ∣ Q.min p q ,
    lower-down-≤ x (Q.min p q) p (O.min≤ p q) lp ,
    lower-down-≤ y (Q.min p q) q (min-below-right p q) lq ∣₁ })
  (lower-inhabited (cutLaws x)) (lower-inhabited (cutLaws y))
upper-inhabited (minCut x y) = PT.map (λ { (q , uq) → q , ∣ inl uq ∣₁ })
  (upper-inhabited (cutLaws x))
lower-rounded (minCut x y) p (lx , ly) = PT.rec2 squash₁
  (λ { (q , pq , lq) (r , pr , lr) → ∣ Q.min q r , below-min p q r pq pr ,
    lower-down-≤ x (Q.min q r) q (O.min≤ q r) lq ,
    lower-down-≤ y (Q.min q r) r (min-below-right q r) lr ∣₁ })
  (lower-rounded (cutLaws x) p lx) (lower-rounded (cutLaws y) p ly)
upper-rounded (minCut x y) q = PT.rec squash₁ λ
  { (inl ux) → PT.map (λ { (p , up , pq) → p , ∣ inl up ∣₁ , pq }) (upper-rounded (cutLaws x) q ux)
  ; (inr uy) → PT.map (λ { (p , up , pq) → p , ∣ inr up ∣₁ , pq }) (upper-rounded (cutLaws y) q uy) }
lower-down (minCut x y) p q pq (lx , ly) =
  lower-down (cutLaws x) p q pq lx , lower-down (cutLaws y) p q pq ly
upper-up (minCut x y) p q pq = PT.map λ
  { (inl ux) → inl (upper-up (cutLaws x) p q pq ux)
  ; (inr uy) → inr (upper-up (cutLaws y) p q pq uy) }
separated (minCut x y) p q (lx , ly) = PT.rec (O.isProp< p q) λ
  { (inl ux) → separated (cutLaws x) p q lx ux
  ; (inr uy) → separated (cutLaws y) p q ly uy }
located (minCut x y) p q pq = PT.rec2 squash₁ combine
  (located (cutLaws x) p q pq) (located (cutLaws y) p q pq)
  where
  combine : (fst (lowerCut x p) ⊎ fst (upperCut x q))
          → (fst (lowerCut y p) ⊎ fst (upperCut y q))
          → ∥ fst (minLower x y p) ⊎ fst (minUpper x y q) ∥₁
  combine (inl lx) (inl ly) = ∣ inl (lx , ly) ∣₁
  combine (inl lx) (inr uy) = ∣ inr ∣ inr uy ∣₁ ∣₁
  combine (inr ux) _ = ∣ inr ∣ inl ux ∣₁ ∣₁

maxCut : (x y : ℝ) → IsDedekindCut (maxLower x y) (maxUpper x y)
lower-inhabited (maxCut x y) = PT.map (λ { (p , lp) → p , ∣ inl lp ∣₁ })
  (lower-inhabited (cutLaws x))
upper-inhabited (maxCut x y) = PT.rec2 squash₁
  (λ { (p , up) (q , uq) → ∣ Q.max p q ,
    upper-up-≤ x p (Q.max p q) (O.≤max p q) up ,
    upper-up-≤ y q (Q.max p q) (max-above-right p q) uq ∣₁ })
  (upper-inhabited (cutLaws x)) (upper-inhabited (cutLaws y))
lower-rounded (maxCut x y) p = PT.rec squash₁ λ
  { (inl lx) → PT.map (λ { (q , pq , lq) → q , pq , ∣ inl lq ∣₁ }) (lower-rounded (cutLaws x) p lx)
  ; (inr ly) → PT.map (λ { (q , pq , lq) → q , pq , ∣ inr lq ∣₁ }) (lower-rounded (cutLaws y) p ly) }
upper-rounded (maxCut x y) q (ux , uy) = PT.rec2 squash₁
  (λ { (p , up , pq) (r , ur , rq) → ∣ Q.max p r ,
    (upper-up-≤ x p (Q.max p r) (O.≤max p r) up ,
     upper-up-≤ y r (Q.max p r) (max-above-right p r) ur) , max-below p r q pq rq ∣₁ })
  (upper-rounded (cutLaws x) q ux) (upper-rounded (cutLaws y) q uy)
lower-down (maxCut x y) p q pq = PT.map λ
  { (inl lx) → inl (lower-down (cutLaws x) p q pq lx)
  ; (inr ly) → inr (lower-down (cutLaws y) p q pq ly) }
upper-up (maxCut x y) p q pq (ux , uy) =
  upper-up (cutLaws x) p q pq ux , upper-up (cutLaws y) p q pq uy
separated (maxCut x y) p q l (ux , uy) = PT.rec (O.isProp< p q)
  (λ { (inl lx) → separated (cutLaws x) p q lx ux
     ; (inr ly) → separated (cutLaws y) p q ly uy }) l
located (maxCut x y) p q pq = PT.rec2 squash₁ combine
  (located (cutLaws x) p q pq) (located (cutLaws y) p q pq)
  where
  combine : (fst (lowerCut x p) ⊎ fst (upperCut x q))
          → (fst (lowerCut y p) ⊎ fst (upperCut y q))
          → ∥ fst (maxLower x y p) ⊎ fst (maxUpper x y q) ∥₁
  combine (inl lx) _ = ∣ inl ∣ inl lx ∣₁ ∣₁
  combine (inr ux) (inl ly) = ∣ inl ∣ inr ly ∣₁ ∣₁
  combine (inr ux) (inr uy) = ∣ inr (ux , uy) ∣₁

minReal maxReal : ℝ → ℝ → ℝ
minReal x y = (minLower x y , minUpper x y) , minCut x y
maxReal x y = (maxLower x y , maxUpper x y) , maxCut x y

-- Non-strict order, expressed symmetrically by inclusion of lower
-- cuts and reverse inclusion of upper cuts.  Its lattice laws below
-- do not use decidable comparison of arbitrary real numbers.
infix 4 _≤ℝ_
_≤ℝ_ : ℝ → ℝ → Type₀
x ≤ℝ y = ((q : ℚ) → fst (lowerCut x q) → fst (lowerCut y q))
       × ((q : ℚ) → fst (upperCut y q) → fst (upperCut x q))

isProp≤ℝ : (x y : ℝ) → isProp (x ≤ℝ y)
isProp≤ℝ x y = isProp× (isPropΠ2 λ q _ → snd (lowerCut y q))
  (isPropΠ2 λ q _ → snd (upperCut x q))

≤ℝ-refl : (x : ℝ) → x ≤ℝ x
≤ℝ-refl x = (λ _ p → p) , (λ _ p → p)

≤ℝ-trans : {x y z : ℝ} → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
≤ℝ-trans (lxy , uyx) (lyz , uzy) = (λ q p → lyz q (lxy q p)) , (λ q p → uyx q (uzy q p))

≤ℝ-antisym : {x y : ℝ} → x ≤ℝ y → y ≤ℝ x → x ≡ y
≤ℝ-antisym (lxy , uyx) (lyx , uxy) = realExt lxy lyx uxy uyx

rational-monotone : (p q : ℚ) → p O.≤ q → rationalReal p ≤ℝ rationalReal q
rational-monotone p q pq = (λ r rp → O.isTrans<≤ r p q rp pq) ,
  (λ r qr → O.isTrans≤< p q r pq qr)

min≤left : (x y : ℝ) → minReal x y ≤ℝ x
min≤left x y = (λ _ → fst) , (λ _ p → ∣ inl p ∣₁)

min≤right : (x y : ℝ) → minReal x y ≤ℝ y
min≤right x y = (λ _ → snd) , (λ _ p → ∣ inr p ∣₁)

≤min : {x y z : ℝ} → z ≤ℝ x → z ≤ℝ y → z ≤ℝ minReal x y
≤min {z = z} (lzx , uxz) (lzy , uyz) =
  (λ q p → lzx q p , lzy q p) , (λ q → PT.rec (snd (upperCut z q)) λ
    { (inl p) → uxz q p ; (inr p) → uyz q p })

left≤max : (x y : ℝ) → x ≤ℝ maxReal x y
left≤max x y = (λ _ p → ∣ inl p ∣₁) , (λ _ → fst)

right≤max : (x y : ℝ) → y ≤ℝ maxReal x y
right≤max x y = (λ _ p → ∣ inr p ∣₁) , (λ _ → snd)

max≤ : {x y z : ℝ} → x ≤ℝ z → y ≤ℝ z → maxReal x y ≤ℝ z
max≤ {z = z} (lxz , uzx) (lyz , uzy) =
  (λ q → PT.rec (snd (lowerCut z q)) λ
    { (inl p) → lxz q p ; (inr p) → lyz q p }) , (λ q p → uzx q p , uzy q p)

min-of-≤ : {x y : ℝ} → x ≤ℝ y → minReal x y ≡ x
min-of-≤ {x} {y} h = ≤ℝ-antisym {x = minReal x y} {y = x}
  (min≤left x y) (≤min {x = x} {y = y} {z = x} (≤ℝ-refl x) h)

max-of-≤ : {x y : ℝ} → x ≤ℝ y → maxReal x y ≡ y
max-of-≤ {x} {y} h = ≤ℝ-antisym {x = maxReal x y} {y = y}
  (max≤ {x = x} {y = y} {z = y} h (≤ℝ-refl y)) (right≤max x y)

ClosedUnitInterval : Type₁
ClosedUnitInterval = Σ[ x ∈ ℝ ] (zeroReal ≤ℝ x) × (x ≤ℝ oneReal)

interval-bounds-isProp : (x : ℝ) → isProp ((zeroReal ≤ℝ x) × (x ≤ℝ oneReal))
interval-bounds-isProp x = isProp× (isProp≤ℝ zeroReal x) (isProp≤ℝ x oneReal)

isSetClosedUnitInterval : isSet ClosedUnitInterval
isSetClosedUnitInterval = isSetΣSndProp isSetℝ interval-bounds-isProp

zero≤one : zeroReal ≤ℝ oneReal
zero≤one = rational-monotone 0 1 (O.<Weaken≤ 0 1 zero<one)

intervalZero intervalOne : ClosedUnitInterval
intervalZero = zeroReal , ≤ℝ-refl zeroReal , zero≤one
intervalOne = oneReal , zero≤one , ≤ℝ-refl oneReal

intervalMin intervalMax : ClosedUnitInterval → ClosedUnitInterval → ClosedUnitInterval
intervalMin (x , zx , xo) (y , zy , yo) = minReal x y ,
  ≤min {x = x} {y = y} {z = zeroReal} zx zy ,
  ≤ℝ-trans {x = minReal x y} {y = x} {z = oneReal} (min≤left x y) xo
intervalMax (x , zx , xo) (y , zy , yo) = maxReal x y ,
  ≤ℝ-trans {x = zeroReal} {y = x} {z = maxReal x y} zx (left≤max x y) ,
  max≤ {x = x} {y = y} {z = oneReal} xo yo

intervalExt : {x y : ClosedUnitInterval} → fst x ≡ fst y → x ≡ y
intervalExt = Σ≡Prop interval-bounds-isProp

interval-min-zero : (x : ClosedUnitInterval) → intervalMin intervalZero x ≡ intervalZero
interval-min-zero x = intervalExt (min-of-≤ (fst (snd x)))

interval-min-one : (x : ClosedUnitInterval) → intervalMin x intervalOne ≡ x
interval-min-one x = intervalExt (min-of-≤ (snd (snd x)))

interval-max-zero : (x : ClosedUnitInterval) → intervalMax intervalZero x ≡ x
interval-max-zero x = intervalExt (max-of-≤ (fst (snd x)))

interval-max-one : (x : ClosedUnitInterval) → intervalMax x intervalOne ≡ intervalOne
interval-max-one x = intervalExt (max-of-≤ (snd (snd x)))
