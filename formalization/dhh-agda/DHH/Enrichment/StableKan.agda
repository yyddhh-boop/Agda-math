{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableKan where

open import Cubical.Foundations.Prelude
open import DHH.Graph
open import DHH.CubicalNerve using (CubicalSet)
open import DHH.Cubical.Kan
open import DHH.StableNerve.Colimit using (N∞)
open import DHH.StableNerve.HornFilling using (N∞-Kan)
open import DHH.StableNerve.IntegerCubical using (directIntegerNerve)
open import DHH.StableNerve.IntegerKan using (directIntegerNerve-Kan)
open import DHH.Enrichment.GraphHom using (HomGraph)

private variable ℓG ℓH : Level

-- CK 的 BOX 内 Hom 图：顶点为实际图同态 G→H，边为逐点相邻。
-- 对它应用稳定 nerve 与几何 DayHom(N∞ G,N∞ H) 是不同构造。
-- HomGraph 已是全部图的实例，故直接应用通用 Kan 定理。
stableHomNerve : Graph ℓG → Graph ℓH → CubicalSet (ℓ-max ℓG ℓH)
stableHomNerve G H = N∞ (HomGraph G H)

stableHomNerve-Kan : (G : Graph ℓG) (H : Graph ℓH)
  → IsKan (stableHomNerve G H)
stableHomNerve-Kan G H = N∞-Kan (HomGraph G H)

-- 整数直接模型的同一局部结论。两图可处于不同 universe，
-- 且无需有限性、枚举 Hom 顶点或选择图映射。
integerStableHomNerve : Graph ℓG → Graph ℓH → CubicalSet (ℓ-max ℓG ℓH)
integerStableHomNerve G H = directIntegerNerve (HomGraph G H)

integerStableHomNerve-Kan : (G : Graph ℓG) (H : Graph ℓH)
  → IsKan (integerStableHomNerve G H)
integerStableHomNerve-Kan G H = directIntegerNerve-Kan (HomGraph G H)

-- 这是原图 Hom 的稳定 nerve 的局部 Kan 性。它没有把
-- nerveHomMap 当作弱等价，也没有证明几何 DayHom 的 Kan 性、
-- 富集函子单位/结合相容、DK 局部化比较或 DHH 本身。
