{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornScalar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_)
open import Cubical.Data.Nat.Properties using (zero∸; ∸+)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ∸-≤; n∸m≡0; ≤-∸-+-cancel)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty using (⊥; isProp⊥)

-- Φ 的标量部分只需要自然数截断减法。先单独证明它的局部
-- 1-Lipschitz 性，后续网格保边证明即可重复调用；不依赖按 m,n
-- 穷举顶点，也不把“落在 horn 中”误当作“保持生成边”。
IsZeroNat : ℕ → Type₀
IsZeroNat zero = Unit
IsZeroNat (suc n) = ⊥

NearNat : ℕ → ℕ → Type₀
NearNat zero zero = Unit
NearNat zero (suc n) = IsZeroNat n
NearNat (suc n) zero = IsZeroNat n
NearNat (suc n) (suc m) = NearNat n m

nearNat-prop : (n m : ℕ) → isProp (NearNat n m)
nearNat-prop zero zero = isPropUnit
nearNat-prop zero (suc zero) = isPropUnit
nearNat-prop zero (suc (suc n)) = isProp⊥
nearNat-prop (suc zero) zero = isPropUnit
nearNat-prop (suc (suc n)) zero = isProp⊥
nearNat-prop (suc n) (suc m) = nearNat-prop n m

nearNat-refl : (n : ℕ) → NearNat n n
nearNat-refl zero = tt
nearNat-refl (suc n) = nearNat-refl n

nearNat-next : (n : ℕ) → NearNat n (suc n)
nearNat-next zero = tt
nearNat-next (suc n) = nearNat-next n

nearNat-prev : (n : ℕ) → NearNat (suc n) n
nearNat-prev zero = tt
nearNat-prev (suc n) = nearNat-prev n

-- 两个变量分别保相邻；不会断言同时改变两个变量也只变化一步。
subtract-near-left : {x y : ℕ} → NearNat x y → (t : ℕ) → NearNat (x ∸ t) (y ∸ t)
subtract-near-left e zero = e
subtract-near-left {zero} {zero} e (suc t) = tt
subtract-near-left {zero} {suc zero} e (suc t) = subst (NearNat zero) (sym (zero∸ t)) tt
subtract-near-left {zero} {suc (suc y)} () (suc t)
subtract-near-left {suc zero} {zero} e (suc t) = subst (λ z → NearNat z zero) (sym (zero∸ t)) tt
subtract-near-left {suc (suc x)} {zero} () (suc t)
subtract-near-left {suc x} {suc y} e (suc t) = subtract-near-left e t

subtract-near-right : (n : ℕ) {x y : ℕ} → NearNat x y → NearNat (n ∸ x) (n ∸ y)
subtract-near-right zero {x} {y} e = subst2 NearNat (sym (zero∸ x)) (sym (zero∸ y)) tt
subtract-near-right (suc n) {zero} {zero} e = nearNat-refl (suc n)
subtract-near-right (suc n) {zero} {suc zero} e = nearNat-prev n
subtract-near-right (suc n) {zero} {suc (suc y)} ()
subtract-near-right (suc n) {suc zero} {zero} e = nearNat-next n
subtract-near-right (suc n) {suc (suc x)} {zero} ()
subtract-near-right (suc n) {suc x} {suc y} e = subtract-near-right n {x = x} {y = y} e

-- missing=true 时，与 paper 的 min(c,max(0,D+c-m)) 相同的候选
-- 算法是 c∸(m∸D)；missing=false 时用区间反射的对称公式。
-- 此模块实际验证下面函数的规律；与 paper β 表达式的比较、
-- 完整网格 Φ 和有限面商上的目标仍是另外的证明义务。
positiveHeight negativeHeight : ℕ → ℕ → ℕ → ℕ
positiveHeight m D c = c ∸ (m ∸ D)
negativeHeight m D c = m ∸ ((m ∸ c) ∸ (m ∸ D))

positive-near-c : (m D : ℕ) {c e : ℕ} → NearNat c e
  → NearNat (positiveHeight m D c) (positiveHeight m D e)
positive-near-c m D {c} {e} h = subtract-near-left {x = c} {y = e} h (m ∸ D)

positive-near-D : (m c : ℕ) {D E : ℕ} → NearNat D E
  → NearNat (positiveHeight m D c) (positiveHeight m E c)
positive-near-D m c {D} {E} h = subtract-near-right c {x = m ∸ D} {y = m ∸ E}
  (subtract-near-right m {x = D} {y = E} h)

negative-near-c : (m D : ℕ) {c e : ℕ} → NearNat c e
  → NearNat (negativeHeight m D c) (negativeHeight m D e)
negative-near-c m D {c} {e} h = subtract-near-right m
  {x = (m ∸ c) ∸ (m ∸ D)} {y = (m ∸ e) ∸ (m ∸ D)}
  (subtract-near-left {x = m ∸ c} {y = m ∸ e}
    (subtract-near-right m {x = c} {y = e} h) (m ∸ D))

negative-near-D : (m c : ℕ) {D E : ℕ} → NearNat D E
  → NearNat (negativeHeight m D c) (negativeHeight m E c)
negative-near-D m c {D} {E} h = subtract-near-right m
  {x = (m ∸ c) ∸ (m ∸ D)} {y = (m ∸ c) ∸ (m ∸ E)}
  (subtract-near-right (m ∸ c) {x = m ∸ D} {y = m ∸ E}
    (subtract-near-right m {x = D} {y = E} h))

positive-bounded : (m D c : ℕ) → c ≤ m → positiveHeight m D c ≤ m
positive-bounded m D c p = ≤-trans (∸-≤ c (m ∸ D)) p
negative-bounded : (m D c : ℕ) → negativeHeight m D c ≤ m
negative-bounded m D c = ∸-≤ m ((m ∸ c) ∸ (m ∸ D))

positive-zero-distance : (m c : ℕ) → c ≤ m → positiveHeight m zero c ≡ zero
positive-zero-distance m c p = n∸m≡0 c m p

positive-large-distance : (m D c : ℕ) → m ≤ D → positiveHeight m D c ≡ c
positive-large-distance m D c p = cong (c ∸_) (n∸m≡0 m D p)

-- 在 opposite missing 面上 c=0，即使 D>0 也直接恢复边界值。
-- 这避免使用 paper Lemma4.4 中过强的“该面上 D=0”推断。
positive-opposite-face : (m D : ℕ) → positiveHeight m D zero ≡ zero
positive-opposite-face m D = zero∸ (m ∸ D)

reflect-involutive : (m c : ℕ) → c ≤ m → m ∸ (m ∸ c) ≡ c
reflect-involutive m c p =
  cong (_∸ (m ∸ c)) (sym (≤-∸-+-cancel {m = c} {n = m} p))
  ∙ ∸+ c (m ∸ c)

negative-zero-distance : (m c : ℕ) → negativeHeight m zero c ≡ m
negative-zero-distance m c = cong (m ∸_) (n∸m≡0 (m ∸ c) m (∸-≤ m c))

negative-large-distance : (m D c : ℕ) → c ≤ m → m ≤ D → negativeHeight m D c ≡ c
negative-large-distance m D c bound far =
  cong (λ d → m ∸ ((m ∸ c) ∸ d)) (n∸m≡0 m D far)
  ∙ reflect-involutive m c bound

negative-opposite-face : (m D : ℕ) → negativeHeight m D m ≡ m
negative-opposite-face m D =
  cong (λ c → m ∸ (c ∸ (m ∸ D))) (n∸m≡0 m m ≤-refl)
  ∙ cong (m ∸_) (zero∸ (m ∸ D))
