{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerLattice where

-- 整数 min/max 是直接的格操作。截断相容按自然数窗口和整数的
-- 构造递归；保边证明仅使用整数的可计算三分比较，不假定任意图
-- 顶点、图映射或数学命题有可判定相等。

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (min to minℕ; max to maxℕ)
open import Cubical.Data.Int using (ℤ; pos; negsuc; sucℤ; predℤ;
  sucDistMin; sucDistMax; minIdem; minSucL; maxIdem; maxSucL)
  renaming (min to minℤ; max to maxℤ; minComm to minCommℤ; maxComm to maxCommℤ)
import Cubical.Data.Int.Order as O
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.StableNerve.Interval
open import DHH.StableNerve.IntervalLaws using (min-zeroR; max-zeroR)
open import DHH.StableNerve.IntegerInterval
open import DHH.StableNerve.IntegerClamp
open import DHH.StableNerve.CenteredInterval

min-positive : (x y : ℕ) → minℤ (pos x) (pos y) ≡ pos (minℕ x y)
min-positive zero y = refl
min-positive (suc x) zero = refl
min-positive (suc x) (suc y) = cong sucℤ (min-positive x y)

max-positive : (x y : ℕ) → maxℤ (pos x) (pos y) ≡ pos (maxℕ x y)
max-positive zero y = refl
max-positive (suc x) zero = refl
max-positive (suc x) (suc y) = cong sucℤ (max-positive x y)

min-negative : (x y : ℕ) → minℤ (negsuc x) (negsuc y) ≡ negsuc (maxℕ x y)
min-negative zero y = refl
min-negative (suc x) zero = refl
min-negative (suc x) (suc y) = cong predℤ (min-negative x y)

max-negative : (x y : ℕ) → maxℤ (negsuc x) (negsuc y) ≡ negsuc (minℕ x y)
max-negative zero y = refl
max-negative (suc x) zero = refl
max-negative (suc x) (suc y) = cong predℤ (max-negative x y)

clampNat-min : (m x y : ℕ)
  → clampNat m (minℕ x y) ≡ minFin (clampNat m x) (clampNat m y)
clampNat-min m zero y = refl
clampNat-min m (suc x) zero = sym (min-zeroR (clampNat m (suc x)))
clampNat-min zero (suc x) (suc y) = refl
clampNat-min (suc m) (suc x) (suc y) = cong fsuc (clampNat-min m x y)

clampNat-max : (m x y : ℕ)
  → clampNat m (maxℕ x y) ≡ maxFin (clampNat m x) (clampNat m y)
clampNat-max m zero y = refl
clampNat-max m (suc x) zero = sym (max-zeroR (clampNat m (suc x)))
clampNat-max zero (suc x) (suc y) = refl
clampNat-max (suc m) (suc x) (suc y) = cong fsuc (clampNat-max m x y)

clamp-min : (m : ℕ) (x y : ℤ)
  → clamp m (minℤ x y) ≡ minFin (clamp m x) (clamp m y)
clamp-min m (pos x) (pos y) = cong (clamp m) (min-positive x y) ∙ clampNat-min m x y
clamp-min m (pos zero) (negsuc y) = refl
clamp-min m (pos (suc x)) (negsuc y) = sym (min-zeroR (clampNat m (suc x)))
clamp-min m (negsuc x) (pos y) = refl
clamp-min m (negsuc x) (negsuc y) = cong (clamp m) (min-negative x y)

clamp-max : (m : ℕ) (x y : ℤ)
  → clamp m (maxℤ x y) ≡ maxFin (clamp m x) (clamp m y)
clamp-max m (pos x) (pos y) = cong (clamp m) (max-positive x y) ∙ clampNat-max m x y
clamp-max m (pos zero) (negsuc y) = refl
clamp-max m (pos (suc x)) (negsuc y) = sym (max-zeroR (clampNat m (suc x)))
clamp-max m (negsuc x) (pos y) = refl
clamp-max m (negsuc x) (negsuc y) = cong (clamp m) (max-negative x y)

up-min : (a : ℕ) (x y : ℤ) → up a (minℤ x y) ≡ minℤ (up a x) (up a y)
up-min zero x y = refl
up-min (suc a) x y = cong sucℤ (up-min a x y) ∙ sucDistMin (up a x) (up a y)

up-max : (a : ℕ) (x y : ℤ) → up a (maxℤ x y) ≡ maxℤ (up a x) (up a y)
up-max zero x y = refl
up-max (suc a) x y = cong sucℤ (up-max a x y) ∙ sucDistMax (up a x) (up a y)

shiftedClamp-min : (a m : ℕ) (x y : ℤ)
  → onVertices (shiftedClamp a m) (minℤ x y)
    ≡ minFin (onVertices (shiftedClamp a m) x) (onVertices (shiftedClamp a m) y)
shiftedClamp-min a m x y = cong (clamp m) (up-min a x y) ∙ clamp-min m (up a x) (up a y)

shiftedClamp-max : (a m : ℕ) (x y : ℤ)
  → onVertices (shiftedClamp a m) (maxℤ x y)
    ≡ maxFin (onVertices (shiftedClamp a m) x) (onVertices (shiftedClamp a m) y)
shiftedClamp-max a m x y = cong (clamp m) (up-max a x y) ∙ clamp-max m (up a x) (up a y)

min-successor-near : (x z : ℤ) → IntegerNear (minℤ x z) (minℤ (sucℤ x) z)
min-successor-near x z with x O.≟ z
... | O.lt p = subst2 IntegerNear (sym (O.≤→min (O.<-weaken p))) (sym (O.≤→min p))
  (integer-successor x)
... | O.eq p = subst (λ w → IntegerNear (minℤ x w) (minℤ (sucℤ x) w)) p
  (subst2 IntegerNear (sym (minIdem x)) (sym (minSucL x)) (integer-refl x))
... | O.gt p = subst2 IntegerNear
  (sym (minCommℤ x z ∙ O.≤→min (O.<-weaken p)))
  (sym (minCommℤ (sucℤ x) z ∙ O.≤→min (O.≤-suc (O.<-weaken p))))
  (integer-refl z)

max-successor-near : (x z : ℤ) → IntegerNear (maxℤ x z) (maxℤ (sucℤ x) z)
max-successor-near x z with x O.≟ z
... | O.lt p = subst2 IntegerNear (sym (O.≤→max (O.<-weaken p))) (sym (O.≤→max p))
  (integer-refl z)
... | O.eq p = subst (λ w → IntegerNear (maxℤ x w) (maxℤ (sucℤ x) w)) p
  (subst2 IntegerNear (sym (maxIdem x)) (sym (maxSucL x)) (integer-successor x))
... | O.gt p = subst2 IntegerNear
  (sym (maxCommℤ x z ∙ O.≤→max (O.<-weaken p)))
  (sym (maxCommℤ (sucℤ x) z ∙ O.≤→max (O.≤-suc (O.<-weaken p))))
  (integer-successor x)

integer-min-near-left : {x y : ℤ} → IntegerNear x y → (z : ℤ)
  → IntegerNear (minℤ x z) (minℤ y z)
integer-min-near-left {x} {y} e z = PT.rec squash₁ (λ where
  (inl p) → subst (IntegerNear (minℤ x z)) (cong (λ w → minℤ w z) p) (integer-refl (minℤ x z))
  (inr (inl p)) → subst (IntegerNear (minℤ x z)) (cong (λ w → minℤ w z) p) (min-successor-near x z)
  (inr (inr p)) → integer-sym (subst (IntegerNear (minℤ y z))
    (cong (λ w → minℤ w z) p) (min-successor-near y z))) e

integer-max-near-left : {x y : ℤ} → IntegerNear x y → (z : ℤ)
  → IntegerNear (maxℤ x z) (maxℤ y z)
integer-max-near-left {x} {y} e z = PT.rec squash₁ (λ where
  (inl p) → subst (IntegerNear (maxℤ x z)) (cong (λ w → maxℤ w z) p) (integer-refl (maxℤ x z))
  (inr (inl p)) → subst (IntegerNear (maxℤ x z)) (cong (λ w → maxℤ w z) p) (max-successor-near x z)
  (inr (inr p)) → integer-sym (subst (IntegerNear (maxℤ y z))
    (cong (λ w → maxℤ w z) p) (max-successor-near y z))) e

integer-min-near-right : (z : ℤ) {x y : ℤ} → IntegerNear x y
  → IntegerNear (minℤ z x) (minℤ z y)
integer-min-near-right z {x} {y} e = subst2 IntegerNear (minCommℤ x z) (minCommℤ y z)
  (integer-min-near-left e z)

integer-max-near-right : (z : ℤ) {x y : ℤ} → IntegerNear x y
  → IntegerNear (maxℤ z x) (maxℤ z y)
integer-max-near-right z {x} {y} e = subst2 IntegerNear (maxCommℤ x z) (maxCommℤ y z)
  (integer-max-near-left e z)
