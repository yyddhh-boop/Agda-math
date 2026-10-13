{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.WholeBoxStages where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.FiniteFaceIndices
import DHH.Cubical.SelectedFinitePresentation as SP
import DHH.StableNerve.SequenceColimit as SC
import DHH.StableNerve.PresentationStages as PS
open import DHH.Graph
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit using (N∞)

-- 这里提升的是整个选面预层的自然变换，包含所有维数的 cell，
-- 不是只把几个代表点搬到同一阶段。有限描述来自面与余维二交集；
-- 其余无限重索引关系由 SelectedFinitePresentation 的比较自动生成。
module Sequence {ℓ : Level} (A : ℕ → CubicalSet ℓ)
  (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s

  module Selected {n : ℕ} (S : FaceSelection n)
    (Nodes : Enumeration (SelectedFacet S))
    (Overlaps : Enumeration (SelectedCodim2 S)) where
    module F = SelectedFaces S
    module M = SP.SelectedPresentation S Nodes Overlaps
    module All = PS.Stages A s
    module L = All.Presented (count Nodes) M.nodeDimension (count Overlaps) M.relations

    record WholeStage (h : CubicalNatural F.complex C.colimitCubical) : Type ℓ where
      field
        stage : ℕ
        stageMap : CubicalNatural F.complex (A stage)
        recovers : stageMap ⋆n C.include stage ≡ h
    open WholeStage public

    -- 输入呈示上的因子化，输出原选面复形上的因子化。
    -- 两个比较映射及其逆式已经被证明，因此这里没有额外假设
    -- “选面复形是有限呈示”的证书，也没有为商点选择代表。
    transfer : (h : CubicalNatural F.complex C.colimitCubical)
      → L.StageFactorization (M.presentationComparison ⋆n h) → WholeStage h
    stage (transfer h d) = L.stage d
    stageMap (transfer h d) = M.presentationComparisonInverse ⋆n L.stageMap d
    recovers (transfer h d) = cubicalNaturalExt
      {A = F.complex} {B = C.colimitCubical}
      {f = stageMap (transfer h d) ⋆n C.include (stage (transfer h d))}
      {g = h}
      (λ m c → cong (λ f → mapCells f m (mapCells M.presentationComparisonInverse m c))
          (L.recovers d)
        ∙ cong (mapCells h m)
          (cong (λ f → mapCells f m c) M.presentationComparison-right))

    factorWhole : (h : CubicalNatural F.complex C.colimitCubical) → ∥ WholeStage h ∥₁
    factorWhole h = PT.map (transfer h)
      (L.factorThroughStage (M.presentationComparison ⋆n h))

  module Boundary (n : ℕ) where
    module Parameters = SP.BoundaryPresentation n
    module Staged = Selected (allFaces n) Parameters.Nodes Parameters.Overlaps
    open Staged public

  module OpenBox {n : ℕ} (missing : Facet n) where
    module Parameters = SP.OpenBoxPresentation missing
    module Staged = Selected (exceptFace missing) Parameters.Nodes Parameters.Overlaps
    open Staged public

-- CK 的真实 N₁→N₂→N₃→… 序列是上述一般构造的直接实例。
-- 有限的是 horn 的生成描述；图 G、其顶点集与所有 nerve cell
-- 都允许无限。截断存在性保持构造性，不添加全局代表选择。
module GraphStages {ℓ : Level} (G : Graph ℓ) where
  module Model = Sequence (Stage G) (stageTransition G)
  open Model public

  openBoxStage : {n : ℕ} (missing : Facet n)
    (box : CubicalNatural (DHH.Cubical.Faces.OpenBox missing) (N∞ G))
    → ∥ Model.OpenBox.WholeStage missing box ∥₁
  openBoxStage missing = Model.OpenBox.factorWhole missing

  boundaryStage : (n : ℕ)
    (boundary : CubicalNatural (DHH.Cubical.Faces.Boundary n) (N∞ G))
    → ∥ Model.Boundary.WholeStage n boundary ∥₁
  boundaryStage n = Model.Boundary.factorWhole n

-- 这不是 Kan 性的证明。下一步还须把阶段 horn 解释为生成的图，
-- 构造足够细的整块网格到该 horn 图的映射，并证明边界三角相容。
