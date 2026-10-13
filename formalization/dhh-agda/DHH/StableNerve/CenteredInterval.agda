{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.CenteredInterval where

-- 研究视角：交替 l/r 不是两套无关的延拓。把阶段 k 的有限区间
-- 放在整数轴上的 [-ceil(k/2), floor(k/2)+1]，两种过渡就都是
-- 「先在大窗口截断，再回到小窗口」。下列等式给出实际相容证书。

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-zero)
open import Cubical.Data.Int using (ℤ; pos; negsuc; sucℤ; predℤ; sucPred; predSuc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true; not)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (PointGraph; boxHom)
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.IntegerInterval
open import DHH.StableNerve.IntegerClamp
open import DHH.StableNerve.Transitions using
  (evenStage; chooseTransition; mapGrid; leftMorph; rightMorph)

-- 平移按步数递归，邻接证明按其三个构造分支递归；这不是整数枚举。
up down : ℕ → ℤ → ℤ
up zero z = z
up (suc a) z = sucℤ (up a z)
down zero z = z
down (suc a) z = predℤ (down a z)

up-pred : (a : ℕ) (z : ℤ) → up a (predℤ z) ≡ predℤ (up a z)
up-pred zero z = refl
up-pred (suc a) z = cong sucℤ (up-pred a z)
  ∙ sucPred (up a z) ∙ sym (predSuc (up a z))

down-suc : (a : ℕ) (z : ℤ) → down a (sucℤ z) ≡ sucℤ (down a z)
down-suc zero z = refl
down-suc (suc a) z = cong predℤ (down-suc a z)
  ∙ predSuc (down a z) ∙ sym (sucPred (down a z))

up-down : (a : ℕ) (z : ℤ) → up a (down a z) ≡ z
up-down zero z = refl
up-down (suc a) z = cong sucℤ (up-pred a (down a z))
  ∙ sucPred (up a (down a z)) ∙ up-down a z

down-up : (a : ℕ) (z : ℤ) → down a (up a z) ≡ z
down-up zero z = refl
down-up (suc a) z = cong predℤ (down-suc a (up a z))
  ∙ predSuc (down a (up a z)) ∙ down-up a z

predecessor-near : {x y : ℤ} → IntegerNear x y
  → IntegerNear (predℤ x) (predℤ y)
predecessor-near {x} {y} = PT.rec squash₁ λ where
  (inl p) → ∣ inl (cong predℤ p) ∣₁
  (inr (inl p)) → ∣ inr (inl
    (sucPred x ∙ sym (predSuc x) ∙ cong predℤ p)) ∣₁
  (inr (inr p)) → ∣ inr (inr
    (sucPred y ∙ sym (predSuc y) ∙ cong predℤ p)) ∣₁

up-near : (a : ℕ) {x y : ℤ} → IntegerNear x y → IntegerNear (up a x) (up a y)
up-near zero e = e
up-near (suc a) e = successor-near (up-near a e)

down-near : (a : ℕ) {x y : ℤ} → IntegerNear x y → IntegerNear (down a x) (down a y)
down-near zero e = e
down-near (suc a) e = predecessor-near (down-near a e)

upMap downMap : ℕ → Hom Iℤ Iℤ
onVertices (upMap a) = up a
preserves (upMap a) = up-near a
onVertices (downMap a) = down a
preserves (downMap a) = down-near a

shiftedInclusion : (a m : ℕ) → Hom (Iₘ m) Iℤ
shiftedInclusion a m = downMap a ∘g finiteIntervalInclusion m

shiftedClamp : (a m : ℕ) → Hom Iℤ (Iₘ m)
shiftedClamp a m = clampMap m ∘g upMap a

shifted-retraction : (a m : ℕ)
  → shiftedClamp a m ∘g shiftedInclusion a m ≡ idHom (Iₘ m)
shifted-retraction a m = homExt λ x →
  cong (clamp m) (up-down a (finiteToInteger x)) ∙ clamp-inclusion x

shifted-injective : (a m : ℕ) {x y : Vertex (Iₘ m)}
  → onVertices (shiftedInclusion a m) x ≡ onVertices (shiftedInclusion a m) y
  → x ≡ y
shifted-injective a m p = finiteToInteger-injective
  (sym (up-down a _) ∙ cong (up a) p ∙ up-down a _)

-- 左扩一个端点时，旧坐标的原点向右移动一步；右扩时原点不变。
-- 这两个截断等式对所有整数成立，包含负区间和端点外的压边。
clamp-left-shift : (m : ℕ) (z : ℤ)
  → leftCollapse (clamp (suc m) (sucℤ z)) ≡ clamp m z
clamp-left-shift m (pos k) = refl
clamp-left-shift m (negsuc zero) = refl
clamp-left-shift m (negsuc (suc k)) = refl

clampNat-right : (m k : ℕ)
  → rightCollapse (clampNat (suc m) k) ≡ clampNat m k
clampNat-right m zero = refl
clampNat-right zero (suc k) = refl
clampNat-right (suc m) (suc k) = cong fsuc (clampNat-right m k)

clamp-right : (m : ℕ) (z : ℤ)
  → rightCollapse (clamp (suc m) z) ≡ clamp m z
clamp-right m (pos k) = clampNat-right m k
clamp-right m (negsuc k) = refl

shiftNext : Bool → ℕ → ℕ
shiftNext true a = suc a
shiftNext false a = a

offset : ℕ → ℕ
offset zero = zero
offset (suc k) = shiftNext (evenStage k) (offset k)

double : ℕ → ℕ
double zero = zero
double (suc a) = suc (suc (double a))

even-double : (a : ℕ) → evenStage (double a) ≡ true
even-double zero = refl
even-double (suc a) = cong (λ b → not (not b)) (even-double a)

odd-double : (a : ℕ) → evenStage (suc (double a)) ≡ false
odd-double a = cong not (even-double a)

-- 两步把左右边界各移一次。这个归纳把「居中」从注释变成可复核的
-- 算术证书：偶数阶段 offset=a，奇数阶段 offset=a+1。
offset-double : (a : ℕ) → offset (double a) ≡ a
offset-double zero = refl
offset-double (suc a) =
  cong (λ b → shiftNext b (offset (suc (double a)))) (odd-double a)
    ∙ cong (λ b → shiftNext b (offset (double a))) (even-double a)
    ∙ cong suc (offset-double a)

offset-suc-double : (a : ℕ) → offset (suc (double a)) ≡ suc a
offset-suc-double a = cong (λ b → shiftNext b (offset (double a))) (even-double a)
  ∙ cong suc (offset-double a)

-- offset 给出 ceil(k/2) 的递归实现。初始窗口依次为 [0,1]、
-- [-1,1]、[-1,2]；所有阶段仍然是原来的 I_(k+1)，只有嵌入平移。
centeredInclusion : (k : ℕ) → Hom (Iₘ (suc k)) Iℤ
centeredInclusion k = shiftedInclusion (offset k) (suc k)

centeredClamp : (k : ℕ) → Hom Iℤ (Iₘ (suc k))
centeredClamp k = shiftedClamp (offset k) (suc k)

centered-retraction : (k : ℕ)
  → centeredClamp k ∘g centeredInclusion k ≡ idHom (Iₘ (suc k))
centered-retraction k = shifted-retraction (offset k) (suc k)

centered-injective : (k : ℕ) {x y : Vertex (Iₘ (suc k))}
  → onVertices (centeredInclusion k) x ≡ onVertices (centeredInclusion k) y → x ≡ y
centered-injective k = shifted-injective (offset k) (suc k)

chooseCollapse : Bool → (m : ℕ) → Hom (Iₘ (suc m)) (Iₘ m)
chooseCollapse true m = leftMap m
chooseCollapse false m = rightMap m

shifted-clamp-step : (b : Bool) (a m : ℕ) (z : ℤ)
  → onVertices (chooseCollapse b m)
      (onVertices (shiftedClamp (shiftNext b a) (suc m)) z)
    ≡ onVertices (shiftedClamp a m) z
shifted-clamp-step true a m z = clamp-left-shift m (up a z)
shifted-clamp-step false a m z = clamp-right m (up a z)

centered-clamp-step : (k : ℕ)
  → chooseCollapse (evenStage k) (suc k) ∘g centeredClamp (suc k)
    ≡ centeredClamp k
centered-clamp-step k = homExt (shifted-clamp-step (evenStage k) (offset k) (suc k))

shiftedGridInclusion : (a m n : ℕ) → Hom (Grid m n) (IntegerGrid n)
shiftedGridInclusion a m zero = idHom PointGraph
shiftedGridInclusion a m (suc n) =
  boxHom (shiftedInclusion a m) (shiftedGridInclusion a m n)

shiftedClampGrid : (a m n : ℕ) → Hom (IntegerGrid n) (Grid m n)
shiftedClampGrid a m zero = idHom PointGraph
shiftedClampGrid a m (suc n) = boxHom (shiftedClamp a m) (shiftedClampGrid a m n)

centeredGridInclusion : (k n : ℕ) → Hom (Grid (suc k) n) (IntegerGrid n)
centeredGridInclusion k = shiftedGridInclusion (offset k) (suc k)

centeredClampGrid : (k n : ℕ) → Hom (IntegerGrid n) (Grid (suc k) n)
centeredClampGrid k = shiftedClampGrid (offset k) (suc k)

centeredGrid-retraction-point : (k n : ℕ) (x : Vertex (Grid (suc k) n))
  → onVertices (centeredClampGrid k n) (onVertices (centeredGridInclusion k n) x) ≡ x
centeredGrid-retraction-point k zero x = refl
centeredGrid-retraction-point k (suc n) (a , x) = cong₂ _,_
  (cong (λ h → onVertices h a) (centered-retraction k))
  (centeredGrid-retraction-point k n x)

centeredGrid-retraction : (k n : ℕ)
  → centeredClampGrid k n ∘g centeredGridInclusion k n ≡ idHom (Grid (suc k) n)
centeredGrid-retraction k n = homExt (centeredGrid-retraction-point k n)

chooseGridCollapse : Bool → (m n : ℕ) → Hom (Grid (suc m) n) (Grid m n)
chooseGridCollapse true m n = mapGrid (leftMorph m) n
chooseGridCollapse false m n = mapGrid (rightMorph m) n

shifted-grid-clamp-step : (b : Bool) (a m n : ℕ) (x : Vertex (IntegerGrid n))
  → onVertices (chooseGridCollapse b m n)
      (onVertices (shiftedClampGrid (shiftNext b a) (suc m) n) x)
    ≡ onVertices (shiftedClampGrid a m n) x
shifted-grid-clamp-step true a m zero x = refl
shifted-grid-clamp-step false a m zero x = refl
shifted-grid-clamp-step true a m (suc n) (z , x) =
  cong₂ _,_ (shifted-clamp-step true a m z) (shifted-grid-clamp-step true a m n x)
shifted-grid-clamp-step false a m (suc n) (z , x) =
  cong₂ _,_ (shifted-clamp-step false a m z) (shifted-grid-clamp-step false a m n x)

centeredGrid-clamp-step : (k n : ℕ)
  → chooseGridCollapse (evenStage k) (suc k) n ∘g centeredClampGrid (suc k) n
    ≡ centeredClampGrid k n
centeredGrid-clamp-step k n = homExt (shifted-grid-clamp-step (evenStage k) (offset k) (suc k) n)

-- 两条射线上的截断有明确端点值。这些证书是以后把窗口稳定性
-- 与论文逐方向的「超过阈值后常值」相比较所需的实际计算引理。
shiftedClamp-lower-ray : (a m d : ℕ)
  → onVertices (shiftedClamp a m) (down a (negsuc d)) ≡ fzero
shiftedClamp-lower-ray a m d = cong (clamp m) (up-down a (negsuc d))

shiftedClamp-upper-ray : (a m d : ℕ)
  → onVertices (shiftedClamp a m) (down a (pos (m + d))) ≡ top m
shiftedClamp-upper-ray a m d = cong (clamp m) (up-down a (pos (m + d)))
  ∙ clamp-at-or-above m d

shiftedClamp-lower-end : (a m : ℕ)
  → onVertices (shiftedClamp a m) (down a (pos zero)) ≡ fzero
shiftedClamp-lower-end a m = cong (clamp m) (up-down a (pos zero))

shiftedClamp-upper-end : (a m : ℕ)
  → onVertices (shiftedClamp a m) (down a (pos m)) ≡ top m
shiftedClamp-upper-end a m = cong (clamp m) (up-down a (pos m))
  ∙ sym (cong (λ t → clamp m (pos t)) (+-zero m))
  ∙ clamp-at-or-above m zero

-- 非负整数要么完整落在窗口内，要么可写成 m+d。证据由同时
-- 缩短 m/k 的递归产生；它不要求全图或整数映射相等的判定器。
clampNat-case : (m t : ℕ)
  → (finiteToInteger (clampNat m t) ≡ pos t) ⊎ (Σ ℕ (λ d → t ≡ m + d))
clampNat-case m zero = inl refl
clampNat-case zero (suc t) = inr (suc t , refl)
clampNat-case (suc m) (suc t) with clampNat-case m t
... | inl p = inl (cong sucℤ p)
... | inr (d , p) = inr (d , cong suc p)
