{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerRealization where

open import Cubical.Foundations.Prelude
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Topology.ContinuousIsoWeak
open import DHH.Realization.CubicalIso
open import DHH.Geometry.RealCubeDiagram
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.IntegerCubical

module Real = CubicalRealization standardCubeDiagram
module RealHomotopy = HomotopyGroups standardCubeGeometry
module RealIsoWeak = IsoWeak standardCubeGeometry

realizedIntegerNerve : Graph (ℓ-suc ℓ-zero) → Top (ℓ-suc ℓ-zero)
realizedIntegerNerve G = Real.realizeCubical (directIntegerNerve G)

-- 把真正的预层自然同构经几何实现送到双向连续的同构。
-- 本定理不是“把比较要求写成一个字段”：四项输入都是实际已经
-- 构造并证明的自然变换及互逆等式，余端生成元消去负责粘接相容。
integerRealizationComparison : (G : Graph (ℓ-suc ℓ-zero))
  → ContinuousIso (Real.realizeCubical (N∞ G)) (realizedIntegerNerve G)
integerRealizationComparison G = Real.realizeCubicalIso {A = N∞ G} {B = directIntegerNerve G}
  (integerNerveComparison G) (integerNerveComparisonInverse G)
  (integerNerveComparison-left G) (integerNerveComparison-right G)

integerRealization-isWeak : (G : Graph (ℓ-suc ℓ-zero))
  → RealHomotopy.WeakHomotopyEquivalence (forward (integerRealizationComparison G))
integerRealization-isWeak G = RealIsoWeak.continuousIso-isWeak
  {X = Real.realizeCubical (N∞ G)} {Y = realizedIntegerNerve G} (integerRealizationComparison G)

integerRealizationGraphMap : {G H : Graph (ℓ-suc ℓ-zero)} → Hom G H
  → Continuous (realizedIntegerNerve G) (realizedIntegerNerve H)
integerRealizationGraphMap {G} {H} f = Real.realizeCubicalMap
  {A = directIntegerNerve G} {B = directIntegerNerve H} (directIntegerGraphMap f)

integerRealization-natural : {G H : Graph (ℓ-suc ℓ-zero)} (f : Hom G H)
  → composeContinuous (integerRealizationGraphMap f) (forward (integerRealizationComparison G))
    ≡ composeContinuous (forward (integerRealizationComparison H))
      (Real.realizeCubicalMap (N∞-map f))
integerRealization-natural {G} {H} f =
  sym (Real.realizeCubical-compose {A = N∞ G} {B = directIntegerNerve G} {C = directIntegerNerve H}
    (integerNerveComparison G) (directIntegerGraphMap f))
  ∙ cong (Real.realizeCubicalMap {A = N∞ G} {B = directIntegerNerve H})
    (integerNerveComparison-graph-natural f)
  ∙ Real.realizeCubical-compose {A = N∞ G} {B = N∞ H} {C = directIntegerNerve H}
    (N∞-map f) (integerNerveComparison H)

-- 比较的范围：有限网格余极限 N∞ 与原文整数稳定 nerve。
-- 此处没有证明原始单位网格 N₁→N∞ 是弱等价，也没有证明
-- 图局部化的 coherent nerve→空间准范畴是等价；这些是其他义务。
