{-# OPTIONS --cubical --safe #-}

module DHH.Statements.Concrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base using (squash₁)
open import DHH.Graph
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Geometry.RealCubeDiagram
open import DHH.Geometry.RealCubeLift
open import DHH.Geometry.RealSimplexLift
open import DHH.Realization.Graph
open import DHH.Statements.Objects
open import DHH.Statements.Full

-- A CLOSED statement type: all three geometric inputs are actual
-- constructed real models.  No caller supplies a geometry, a weak
-- equivalence predicate, a mapping object, or a comparison map.
--
-- This is the all-arrow-resolution formulation.  Its comparison with
-- the classical DK localization and the original enriched-graph DHH
-- remains a separate theorem, not an inhabitant silently assumed here.
-- The graph vertices live in Type₁; all graph sizes in that universe,
-- all dimensions, and all graph pairs are quantified over.
module Geometric = Statement standardCubeGeometry
  standardMappingSimplexDiagram standardMappingCubeGeometry
module Realization = GraphRealization standardCubeGeometry
module Objects = ObjectStatement standardCubeGeometry
module MappingHomotopy = HomotopyGroups standardMappingCubeGeometry

open Realization public using (NG; NG-map; NG-functor; W)
open Geometric public using
  (GraphMappingCategory; SpaceMappingCategory; enrichedComparison;
   GraphMappingSpace; SpaceMappingSpace; mappingComparison)

-- 研究取向：优先从递归构造、结构归纳、自然性和泛性质研究此陈述。
-- 定义 NG、W 和 mappingComparison 未提供 W 的判定器或任意空间的
-- 图模型生成算法；对象项的命题截断也不能直接读取为输出具体图的程序。
-- 具体的算法性贡献应另标输入表示、递归/终止依据、保持的结构和正确性。
DHH : Type₃
DHH = Geometric.DHHStatement

ObjectRealization : Type₂
ObjectRealization = Objects.ObjectDHH

AllMappingComparisons : Type₃
AllMappingComparisons = (G H : Graph (ℓ-suc ℓ-zero))
  → MappingHomotopy.WeakHomotopyEquivalence (mappingComparison G H)

object-realization : DHH → ObjectRealization
object-realization = Geometric.essentially-surjective

mapping-equivalences : DHH → AllMappingComparisons
mapping-equivalences = Geometric.fully-faithful

makeDHH : ObjectRealization → AllMappingComparisons → DHH
Geometric.essentially-surjective (makeDHH objects maps) = objects
Geometric.fully-faithful (makeDHH objects maps) = maps

-- Proof irrelevance of the statement itself.  This does not provide
-- either of its two required proofs.
DHH-isProp : isProp DHH
Geometric.essentially-surjective (DHH-isProp p q i) X =
  squash₁ (Geometric.essentially-surjective p X)
    (Geometric.essentially-surjective q X) i
Geometric.fully-faithful (DHH-isProp p q i) G H =
  MappingHomotopy.weak-isProp (mappingComparison G H)
    (Geometric.fully-faithful p G H) (Geometric.fully-faithful q G H) i
