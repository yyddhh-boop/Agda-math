{-# OPTIONS --cubical --safe #-}

module DHH.StableNerve.GeometricComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.Kan
open import DHH.PresheafInterop
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Geometry.RealCubeDiagram
open import DHH.Realization.Coend
open import DHH.Realization.Graph
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.UnitComparison
open import DHH.StableNerve.HornFilling using (N∞-Kan)

-- 把已构造的组合比较接到同一真实立方体几何上。
-- 逐 cell 使用原 N₁→N∞ 的程序，几何坐标不变；余端泛性质负责粘接。
-- 这里没有另选一个未知“弱等价”作比较映射。
module Raw = GraphRealization standardCubeGeometry
module StableSpace (G : Graph (ℓ-suc ℓ-zero)) =
  Realization standardCubeDiagram (asPresheaf (N∞ G))
module RealHomotopy = HomotopyGroups standardCubeGeometry

realizeStable : Graph (ℓ-suc ℓ-zero) → Top (ℓ-suc ℓ-zero)
realizeStable G = StableSpace.realize G isSetℕ

realizeStableMap : {G H : Graph (ℓ-suc ℓ-zero)} → Hom G H
  → Continuous (realizeStable G) (realizeStable H)
realizeStableMap f = RealizationMap.realizeMap isSetℕ standardCubeDiagram
  (asNaturalTransformation (N∞-map f))

rawToStable : (G : Graph (ℓ-suc ℓ-zero)) → Continuous (Raw.NG G) (realizeStable G)
rawToStable G = RealizationMap.realizeMap isSetℕ standardCubeDiagram
  (asNaturalTransformation (N₁-to-N∞ G))

-- 证明跟随构造：在任意维 cell 上检查自然性，然后用商消去推广到全空间。
-- 这没有逐点枚举，也没有假设原/稳定实现已经等价。
rawToStable-natural : {G H : Graph (ℓ-suc ℓ-zero)} (f : Hom G H)
  → composeContinuous (realizeStableMap f) (rawToStable G)
    ≡ composeContinuous (rawToStable H) (Raw.NG-map f)
rawToStable-natural {H = H} f = continuousExt
  (SQ.elimProp (λ _ → carrier-isSet (realizeStable H) _ _)
    (λ { (n , c , t) → cong (λ d → StableSpace.point H n d t)
      (cong (λ η → mapCells η n c) (N₁-to-N∞-natural f)) }))

-- 两个基础定理各自陈述。HornFilling 已提供第一个的证明项，
-- 第二个仍是待证 TYPE；两者均非 rawToStable 构造的假设。
-- 第一个要求所有维数的缺面都可填；第二个要求既定连续映射是全维弱等价。
-- 它们不是 DHH 的对象实现性或映射完全忠实性本身。
StableKanClaim : Type₂
StableKanClaim = (G : Graph (ℓ-suc ℓ-zero)) → IsKan (N∞ G)

stableKan : StableKanClaim
stableKan G = N∞-Kan G

RawToStableWeakEquivalenceClaim : Type₂
RawToStableWeakEquivalenceClaim = (G : Graph (ℓ-suc ℓ-zero))
  → RealHomotopy.WeakHomotopyEquivalence (rawToStable G)

-- Kan 性现由完整 horn 阶段提升、实际收缩和全部边界恢复得到。
-- rawToStable 的弱等价性仍需独立证明，不能由自然性或 Kan 性推出。
