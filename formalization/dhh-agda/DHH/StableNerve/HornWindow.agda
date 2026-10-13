{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornWindow where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Cubical.Data.FinData using (Fin; toℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import DHH.Graph
open import DHH.Cubes using (boxHom)
open import DHH.StableNerve.Interval
open import DHH.StableNerve.IntegerClamp using (clampNat; clamp-inclusion)
open import DHH.StableNerve.CenteredInterval using (clampNat-right)
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Padding
open import DHH.StableNerve.HornScalar
open import DHH.StableNerve.HornInterval using (finite-near-nat)
open import DHH.StableNerve.HornDistance

coordinate-near : (a b : ℕ) {v w : ℕ} → NearNat v w
  → Near (windowCoordinate a b v) (windowCoordinate a b w)
coordinate-near a b {v} {w} e with windowEdge a b {v} {w} e
... | leftEdge p q d = subst2 (Near {b}) (sym p) (sym q) tt
... | rightEdge p q d = subst2 (Near {b}) (sym p) (sym q) (near-refl (top b))
... | middleEdge p q c = c

-- 固定窗口规则成为实际图同态；来源上界 r 可任意，不要求
-- 每个函数固定两个端点。三倍窗口随后与已证 IntervalMorph 识别。
coordinateMap : (a b r : ℕ) → Hom (Iₘ r) (Iₘ b)
onVertices (coordinateMap a b r) x = windowCoordinate a b (toℕ x)
preserves (coordinateMap a b r) {x} {y} e = coordinate-near a b
  {toℕ x} {toℕ y} (finite-near-nat {r} {x} {y} e)

windowGrid : (a b r n : ℕ) → Hom (Grid r n) (Grid b n)
windowGrid a b r zero = idHom _
windowGrid a b r (suc n) = boxHom (coordinateMap a b r) (windowGrid a b r n)

-- 右删除与任意自然数截断相容。把 v 先截在大窗口，再递归
-- 删除右 padding，恰好等于一次截在小窗口；无需取有限代表表。
right-padding-clamp : (k m v : ℕ)
  → onVertices (intervalMap (removeRightPadding k m)) (clampNat (k + m) v)
    ≡ clampNat m v
right-padding-clamp zero m v = refl
right-padding-clamp (suc k) m v =
  cong (onVertices (intervalMap (removeRightPadding k m))) (clampNat-right (k + m) v)
  ∙ right-padding-clamp k m v

left-padding-clamp : (k m v : ℕ)
  → onVertices (intervalMap (removeLeftPadding k m)) (clampNat (k + m) v)
    ≡ windowCoordinate k m v
left-padding-clamp zero m v = refl
left-padding-clamp (suc k) m zero = left-padding-clamp k m zero ∙ coordinate-zero k m
left-padding-clamp (suc k) m (suc v) = left-padding-clamp k m v

left-padding-value : (k m : ℕ) (x : Fin (suc (k + m)))
  → onVertices (intervalMap (removeLeftPadding k m)) x
    ≡ windowCoordinate k m (toℕ x)
left-padding-value k m x =
  cong (onVertices (intervalMap (removeLeftPadding k m))) (sym (clamp-inclusion x))
  ∙ left-padding-clamp k m (toℕ x)

-- 左、右 padding 组合的数值公式。次序选 a+(t+b)，让右删除
-- 的源尺寸 t+b 定义性匹配；对称 a=b=t=m 即是原 middleCollapse。
padding-coordinate : (a b t : ℕ) (x : Fin (suc (a + (t + b))))
  → onVertices (intervalMap
      (composeMorph (removeLeftPadding a (t + b)) (removeRightPadding t b))) x
    ≡ windowCoordinate a b (toℕ x)
padding-coordinate a b t x =
  cong (onVertices (intervalMap (removeRightPadding t b)))
    (left-padding-value a (t + b) x ∙ coordinate-formula a (t + b) (toℕ x))
  ∙ right-padding-clamp t b (toℕ x ∸ a)
  ∙ sym (coordinate-formula a b (toℕ x))

middle-value : (m : ℕ) (x : Fin (suc (m + (m + m))))
  → onVertices (intervalMap (middleCollapse m)) x ≡ windowCoordinate m m (toℕ x)
middle-value m = padding-coordinate m m m

middle-coordinate-map : (m : ℕ)
  → intervalMap (middleCollapse m) ≡ coordinateMap m m (m + (m + m))
middle-coordinate-map m = homExt (middle-value m)

-- 同一一维公式按坐标数递归，得到全部维数的实际图等式。
-- 这把“递归删除 padding”和“算式 clamp(v-m)”连成同一个程序。
middle-grid-value : (m n : ℕ) (x : Vertex (Grid (m + (m + m)) n))
  → onVertices (middleGrid m n) x ≡ onVertices (windowGrid m m (m + (m + m)) n) x
middle-grid-value m zero x = refl
middle-grid-value m (suc n) (a , x) = cong₂ _,_ (middle-value m a) (middle-grid-value m n x)

middle-grid-formula : (m n : ℕ)
  → middleGrid m n ≡ windowGrid m m (m + (m + m)) n
middle-grid-formula m n = homExt (middle-grid-value m n)

-- 由于 middleCollapse 已带完整端点、min、max 和立方自然性，
-- 上述识别覆盖全部连接算子；仍未给特殊坐标高度或整个 Φ。
