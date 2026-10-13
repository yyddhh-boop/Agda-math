{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.Padding where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma
open import DHH.Graph
open import DHH.CubeCategory using (CubicalMap)
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.Nerve using (gridAction)
open import DHH.StableNerve.Transitions

-- 把单位区间操作组合成任意有限 padding 的删除程序。
-- 尺寸写成 k+m，按 k 递归时来源尺寸定义性地变为 suc(k+m)，
-- 因而不需要强迫自然数加法结合/交换等式成为 refl。
identityMorph : (m : ℕ) → IntervalMorph m m
intervalMap (identityMorph m) = idHom (Iₘ m)
endpoints (identityMorph m) b = refl
minimum (identityMorph m) a b = refl
maximum (identityMorph m) a b = refl

composeMorph : {r s t : ℕ} → IntervalMorph r s → IntervalMorph s t → IntervalMorph r t
intervalMap (composeMorph M N) = intervalMap N ∘g intervalMap M
endpoints (composeMorph M N) b =
  cong (onVertices (intervalMap N)) (endpoints M b) ∙ endpoints N b
minimum (composeMorph M N) a b =
  cong (onVertices (intervalMap N)) (minimum M a b)
  ∙ minimum N (onVertices (intervalMap M) a) (onVertices (intervalMap M) b)
maximum (composeMorph M N) a b =
  cong (onVertices (intervalMap N)) (maximum M a b)
  ∙ maximum N (onVertices (intervalMap M) a) (onVertices (intervalMap M) b)

-- 按坐标数递归证明：逐坐标执行恒等/复合，等于整个网格的
-- 恒等/复合。后面的图商只需消费这两个结构性证明。
mapGrid-identity : (m n : ℕ) → mapGrid (identityMorph m) n ≡ idHom (Grid m n)
mapGrid-identity m zero = homExt (λ _ → refl)
mapGrid-identity m (suc n) = homExt λ { (a , x) →
  cong (a ,_) (cong (λ h → onVertices h x) (mapGrid-identity m n)) }

mapGrid-compose : {r s t : ℕ} (M : IntervalMorph r s) (N : IntervalMorph s t) (n : ℕ)
  → mapGrid (composeMorph M N) n ≡ mapGrid N n ∘g mapGrid M n
mapGrid-compose M N zero = homExt (λ _ → refl)
mapGrid-compose M N (suc n) = homExt λ { (a , x) →
  cong (onVertices (intervalMap N) (onVertices (intervalMap M) a) ,_)
    (cong (λ h → onVertices h x) (mapGrid-compose M N n)) }

removeLeftPadding removeRightPadding : (k m : ℕ) → IntervalMorph (k + m) m
removeLeftPadding zero m = identityMorph m
removeLeftPadding (suc k) m = composeMorph (leftMorph (k + m)) (removeLeftPadding k m)
removeRightPadding zero m = identityMorph m
removeRightPadding (suc k) m = composeMorph (rightMorph (k + m)) (removeRightPadding k m)

-- 三倍网格的中间窗口：先删除左边 m 层，再删除右边 m 层。
-- 每次只调用已经带保边/端点/min/max证书的一步操作，递归次数为 m。
middleCollapse : (m : ℕ) → IntervalMorph (m + (m + m)) m
middleCollapse m = composeMorph (removeLeftPadding m (m + m)) (removeRightPadding m m)

middleGrid : (m n : ℕ) → Hom (Grid (m + (m + m)) n) (Grid m n)
middleGrid m n = mapGrid (middleCollapse m) n

-- 与全部面、退化和 min/max connection 相容；不是只检查面限制。
middleGrid-natural : (m : ℕ) {i j : ℕ} (u : CubicalMap i j)
  → middleGrid m j ∘g gridAction (m + (m + m)) u
    ≡ gridAction m u ∘g middleGrid m i
middleGrid-natural m u = gridAction-natural (middleCollapse m) u

-- 到通常 min/max 截断算式的数值识别是另一个定理。本模块实际
-- 构造保边的三倍窗口压缩及全部立方自然性，仍未构造 horn 收缩。
