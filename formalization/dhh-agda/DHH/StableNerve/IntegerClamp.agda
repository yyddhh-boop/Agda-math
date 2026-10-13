{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerClamp where

-- 研究视角：用有限窗口 + 一个统一延拓规则来描述无限网格上的映射。
-- 这里的回缩等式说明窗口内的信息完整保留；后续应研究窗口平移、
-- 扩大与立方算子的交换规律，以构造模型比较，而不是枚举更多网格点。
-- 这些相容比较是候选下一步，本文件末尾明确保留尚未完成的义务。

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Int using (ℤ; pos; negsuc; sucℤ)
open import Cubical.Data.FinData using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
import Cubical.HITs.PropositionalTruncation.Properties as PT

open import DHH.Graph
open import DHH.Cubes using (PointGraph; boxHom)
open import DHH.StableNerve.Interval using (Iₘ; Near; top; near-refl; near-prop)
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.IntegerInterval

private
  variable
    ℓ : Level

-- 先处理非负坐标：输入 0 时输出 0；窗口已耗尽时停在端点；
-- 否则把窗口上界和输入同时减一，递归结果再加一个 fsuc。
-- 递归在 m 与 k 的真子项上进行，不枚举区间或整数集合。
clampNat : (m k : ℕ) → Fin (suc m)
clampNat m zero = fzero
clampNat zero (suc k) = fzero
clampNat (suc m) (suc k) = fsuc (clampNat m k)

clamp : (m : ℕ) → ℤ → Fin (suc m)
clamp m (pos k) = clampNat m k
clamp m (negsuc k) = fzero

clamp-zero : (m : ℕ) → clamp m (pos zero) ≡ fzero
clamp-zero m = refl

clamp-negative : (m k : ℕ) → clamp m (negsuc k) ≡ fzero
clamp-negative m k = refl

-- 对任意 k，上界以后的 m+k 都截为 top m；这包括上界本身。
-- 因而窗口 [0,m] 外的两端分别保持常值 0 和 m。
clamp-at-or-above : (m k : ℕ) → clamp m (pos (m + k)) ≡ top m
clamp-at-or-above zero zero = refl
clamp-at-or-above zero (suc k) = refl
clamp-at-or-above (suc m) k = cong fsuc (clamp-at-or-above m k)

-- 保边只需证明相邻自然数经截断后仍相邻。
-- 在内点，剥去共同 fsuc 后由更小窗口的递归证明解决；
-- 触到端点时，一条边可能压成自环，这正是自反图允许的情况。
clampNat-successor : (m k : ℕ) → Near (clampNat m k) (clampNat m (suc k))
clampNat-successor zero zero = tt
clampNat-successor zero (suc k) = tt
clampNat-successor (suc m) zero = tt
clampNat-successor (suc m) (suc k) = clampNat-successor m k

clamp-successor : (m : ℕ) (z : ℤ) → Near (clamp m z) (clamp m (sucℤ z))
clamp-successor m (pos k) = clampNat-successor m k
clamp-successor m (negsuc zero) = tt
clamp-successor m (negsuc (suc k)) = tt

-- 整数邻接的截断只消去到命题 Near：相等分支用自环，
-- 后继分支用上面的计算，反向后继分支再使用无向对称性。
clamp-near : (m : ℕ) {x y : ℤ} → IntegerNear x y → Near (clamp m x) (clamp m y)
clamp-near m {x} {y} = PT.rec (near-prop (clamp m x) (clamp m y)) λ where
  (inl p) → subst (Near (clamp m x)) (cong (clamp m) p) (near-refl (clamp m x))
  (inr (inl p)) → subst (Near (clamp m x)) (cong (clamp m) p) (clamp-successor m x)
  (inr (inr p)) → adj-sym (Iₘ m) {x = clamp m y} {y = clamp m x}
    (subst (Near (clamp m y)) (cong (clamp m) p) (clamp-successor m y))

clampMap : (m : ℕ) → Hom Iℤ (Iₘ m)
onVertices (clampMap m) = clamp m
preserves (clampMap m) = clamp-near m

-- 有限区间内的坐标不会碰到截断边界：每剥去一个 fsuc，
-- 就把「嵌入后截断」缩减成小一阶的同一问题。
clamp-inclusion : {m : ℕ} (x : Fin (suc m)) → clamp m (finiteToInteger x) ≡ x
clamp-inclusion fzero = refl
clamp-inclusion {suc m} (fsuc x) = cong fsuc (clamp-inclusion x)

clamp-retraction : (m : ℕ) → clampMap m ∘g finiteIntervalInclusion m ≡ idHom (Iₘ m)
clamp-retraction m = homExt clamp-inclusion

-- 对每一个整数坐标执行同一截断；boxHom 已证明只改一个
-- 坐标的 BOX 邻接仍被保持。0 维是单点上的恒等映射。
clampGrid : (m n : ℕ) → Hom (IntegerGrid n) (Grid m n)
clampGrid m zero = idHom PointGraph
clampGrid m (suc n) = boxHom (clampMap m) (clampGrid m n)

clampGrid-inclusion : (m n : ℕ) (x : Vertex (Grid m n))
  → onVertices (clampGrid m n) (onVertices (finiteGridInclusion m n) x) ≡ x
clampGrid-inclusion m zero x = refl
clampGrid-inclusion m (suc n) (a , x) =
  cong₂ _,_ (clamp-inclusion a) (clampGrid-inclusion m n x)

clampGrid-retraction : (m n : ℕ)
  → clampGrid m n ∘g finiteGridInclusion m n ≡ idHom (Grid m n)
clampGrid-retraction m n = homExt (clampGrid-inclusion m n)

-- 延拓算法：先把整数网格的坐标逐个截回有限窗口，再调用 f。
-- 这是对任意给定图 G、任意维数 n 的实际图映射构造。
extendToIntegerGrid : {G : Graph ℓ} (m n : ℕ)
  → Hom (Grid m n) G → Hom (IntegerGrid n) G
extendToIntegerGrid m n f = f ∘g clampGrid m n

restrictToFiniteGrid : {G : Graph ℓ} (m n : ℕ)
  → Hom (IntegerGrid n) G → Hom (Grid m n) G
restrictToFiniteGrid m n f = f ∘g finiteGridInclusion m n

-- 延拓后限制精确恢复原图映射；只需把坐标回缩等式送入 f，
-- 邻接证明的相等由 Hom 的外延性统一处理。
restrict-extend : {G : Graph ℓ} (m n : ℕ) (f : Hom (Grid m n) G)
  → restrictToFiniteGrid m n (extendToIntegerGrid m n f) ≡ f
restrict-extend m n f = homExt λ x →
  cong (onVertices f) (clampGrid-inclusion m n x)

-- 本模块给出固定 [0,m]^n 窗口的延拓候选：固定其余坐标时，
-- 每个坐标越过端点后不再改变函数值，并非整个窗口外都取同一值。
-- 尚未构造 CK 交替/居中窗口的相容比较，也未证明稳定 nerve 的
-- Kan 性或其几何实现与原 nerve 的比较等价。
