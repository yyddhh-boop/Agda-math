{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerInterval where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; sucℤ; predℤ; isSetℤ; injPos; sucPred; predSuc)
open import Cubical.Data.FinData using (Fin; toℕ; inj-toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT

open import DHH.Graph
open import DHH.Cubes using (PointGraph; boxHom)
open import DHH.StableNerve.Interval using (Iₘ; Near; top)
open import DHH.StableNerve.Grid using (Grid)

-- 实际的双向无限整数区间：顶点就是 ℤ，邻接是相等或相差一个后继。
-- 第三个分支把后继方向反转，等价于「y 是 x 的前驱」。
-- 命题截断只忘记邻接见证，不添加边，也不把顶点截断成有限集合。
IntegerNear : ℤ → ℤ → Type₀
IntegerNear x y = ∥ (x ≡ y) ⊎ ((sucℤ x ≡ y) ⊎ (sucℤ y ≡ x)) ∥₁

integer-refl : (x : ℤ) → IntegerNear x x
integer-refl x = ∣ inl refl ∣₁

integer-sym : {x y : ℤ} → IntegerNear x y → IntegerNear y x
integer-sym = PT.rec squash₁ λ where
  (inl p) → ∣ inl (sym p) ∣₁
  (inr (inl p)) → ∣ inr (inr p) ∣₁
  (inr (inr p)) → ∣ inr (inl p) ∣₁

integer-successor : (x : ℤ) → IntegerNear x (sucℤ x)
integer-successor x = ∣ inr (inl refl) ∣₁

integer-predecessor : (x : ℤ) → IntegerNear x (predℤ x)
integer-predecessor x = ∣ inr (inr (sucPred x)) ∣₁

Iℤ : Graph ℓ-zero
Vertex Iℤ = ℤ
vertex-isSet Iℤ = isSetℤ
Adj Iℤ = IntegerNear
adj-isProp Iℤ _ _ = squash₁
adj-refl Iℤ = integer-refl
adj-sym Iℤ = integer-sym

-- 整条整数区间向右平移一步仍保持邻接。
-- 算法只看邻接的三个构造分支；对每个等式施加 sucℤ 即可。
-- 消去截断合法，因为目标 IntegerNear 也是命题。
successor-near : {x y : ℤ} → IntegerNear x y → IntegerNear (sucℤ x) (sucℤ y)
successor-near = PT.rec squash₁ λ where
  (inl p) → ∣ inl (cong sucℤ p) ∣₁
  (inr (inl p)) → ∣ inr (inl (cong sucℤ p)) ∣₁
  (inr (inr p)) → ∣ inr (inr (cong sucℤ p)) ∣₁

successorMap : Hom Iℤ Iℤ
onVertices successorMap = sucℤ
preserves successorMap = successor-near

-- 有限区间 [0,m] 的嵌入由有限序号读取算法给出：0 ↦ 0，
-- 每读一个 fsuc 就向右走一步。m 是输入参数，没有逐个枚举 m。
finiteToInteger : {m : ℕ} → Fin (suc m) → ℤ
finiteToInteger x = pos (toℕ x)

finiteToInteger-injective : {m : ℕ} {x y : Fin (suc m)}
  → finiteToInteger x ≡ finiteToInteger y → x ≡ y
finiteToInteger-injective p = inj-toℕ (injPos p)

-- 递归证明保持边：两端都有 fsuc 时先剥掉共同的第一步，
-- 对更短区间调用自身，再用 successor-near 平移回来。
-- 触到 0 的分支只可能是自环或 0—1；其余由 Near 的空类型排除。
finiteToInteger-near : {m : ℕ} {x y : Fin (suc m)}
  → Near x y → IntegerNear (finiteToInteger x) (finiteToInteger y)
finiteToInteger-near {x = fzero} {fzero} e = integer-refl (pos zero)
finiteToInteger-near {suc m} {fzero} {fsuc fzero} e = integer-successor (pos zero)
finiteToInteger-near {suc m} {fzero} {fsuc (fsuc y)} ()
finiteToInteger-near {suc m} {fsuc fzero} {fzero} e = integer-sym (integer-successor (pos zero))
finiteToInteger-near {suc m} {fsuc (fsuc x)} {fzero} ()
finiteToInteger-near {suc m} {fsuc x} {fsuc y} e =
  successor-near (finiteToInteger-near {m} {x} {y} e)

finiteIntervalInclusion : (m : ℕ) → Hom (Iₘ m) Iℤ
onVertices (finiteIntervalInclusion m) = finiteToInteger
preserves (finiteIntervalInclusion m) {x = x} {y = y} =
  finiteToInteger-near {m} {x} {y}

finiteToInteger-top : (m : ℕ) → finiteToInteger (top m) ≡ pos m
finiteToInteger-top zero = refl
finiteToInteger-top (suc m) = cong sucℤ (finiteToInteger-top m)

-- 维数递归仍然用 BOX：每条边只改变一个整数坐标。
-- 0 维是单点；n+1 维是在 n 维前再放一个整数坐标。
IntegerGrid : ℕ → Graph ℓ-zero
IntegerGrid zero = PointGraph
IntegerGrid (suc n) = Iℤ BOX IntegerGrid n

finiteGridInclusion : (m n : ℕ) → Hom (Grid m n) (IntegerGrid n)
finiteGridInclusion m zero = idHom PointGraph
finiteGridInclusion m (suc n) =
  boxHom (finiteIntervalInclusion m) (finiteGridInclusion m n)

-- 嵌入的单射性同样按坐标递归：相等的坐标对给出首坐标相等，
-- 尾坐标交给归纳假设；无需列出有限网格的全部顶点。
finiteGridInclusion-injective : (m n : ℕ) {x y : Vertex (Grid m n)}
  → onVertices (finiteGridInclusion m n) x ≡ onVertices (finiteGridInclusion m n) y
  → x ≡ y
finiteGridInclusion-injective m zero p = p
finiteGridInclusion-injective m (suc n) p = cong₂ _,_
  (finiteToInteger-injective (cong fst p))
  (finiteGridInclusion-injective m n (cong snd p))

-- 本模块只建立实际整数图、有限网格的嵌入及其证明。
-- 稳定性条件、稳定整数 nerve、Kan 填充与几何实现比较仍须另行构造。
