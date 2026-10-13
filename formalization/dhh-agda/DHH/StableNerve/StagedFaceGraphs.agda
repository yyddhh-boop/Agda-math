{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.StagedFaceGraphs where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.FiniteFaceIndices
import DHH.Cubical.SelectedFinitePresentation as SP
import DHH.Cubical.SelectedGraphPresentation as SG
import DHH.StableNerve.WholeBoxStages as WS
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit

-- Kan 构造的输入现已成为实际图映射。程序先同步有限面呈示的
-- 全部关系，再用网格图的泛性质解释它。输出图的边按面生成，
-- 不会在粘接后自动补入缺失面的边，也不要求目标图可枚举。
module FaceGraphs {ℓ : Level} (G : Graph ℓ) where
  module Sequence = WS.Sequence (Stage G) (stageTransition G)

  module Selected {n : ℕ} (S : FaceSelection n)
    (Nodes : Enumeration (SelectedFacet S))
    (Overlaps : Enumeration (SelectedCodim2 S)) where
    module F = SelectedFaces S
    module W = Sequence.Selected S Nodes Overlaps
    module V (m : ℕ) = SG.SelectedGraph m S Nodes Overlaps

    record Representation (h : CubicalNatural F.complex (N∞ G)) : Type ℓ where
      constructor representation
      field
        stage : ℕ
        graphMap : Hom (V.graph (suc stage)) G
        recovers : V.toSelected (suc stage) G graphMap ⋆n includeStage G stage ≡ h
    open Representation public

    stageRecovery : (k : ℕ) (x : CubicalNatural F.complex (Stage G k))
      → V.toSelected (suc k) G (V.fromSelected (suc k) G x)
          ⋆n includeStage G k ≡ x ⋆n includeStage G k
    stageRecovery k x = cubicalNaturalExt
      {A = F.complex} {B = N∞ G}
      {f = V.toSelected (suc k) G (V.fromSelected (suc k) G x) ⋆n includeStage G k}
      {g = x ⋆n includeStage G k}
      (λ n c → cong (mapCells (includeStage G k) n)
          (cong (λ f → mapCells f n c) (V.to-from (suc k) G x)))

    fromWhole : (h : CubicalNatural F.complex (N∞ G))
      → W.WholeStage h → Representation h
    fromWhole h d = representation (W.stage d)
      (V.fromSelected (suc (W.stage d)) G (W.stageMap d))
      (stageRecovery (W.stage d) (W.stageMap d) ∙ W.recovers d)

    graphRepresentation : (h : CubicalNatural F.complex (N∞ G)) → ∥ Representation h ∥₁
    graphRepresentation h = PT.map (fromWhole h) (W.factorWhole h)

  module Boundary (n : ℕ) where
    module Parameters = SP.BoundaryPresentation n
    module Constructed = Selected (allFaces n) Parameters.Nodes Parameters.Overlaps
    open Constructed public

  module OpenBox {n : ℕ} (missing : Facet n) where
    module Parameters = SP.OpenBoxPresentation missing
    module Constructed = Selected (exceptFace missing) Parameters.Nodes Parameters.Overlaps
    open Constructed public

-- Representation 不是 filler：尚须生成整块扩网格到 V.graph 的保边
-- 映射，并证明它在所有已选面的限制与阶段过渡相容。这里真实完成
-- 了任意 horn 映射→有限阶段 horn 图映射这段构造，不假定后一步。
