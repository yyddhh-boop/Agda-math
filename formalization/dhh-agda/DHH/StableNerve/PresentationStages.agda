{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.PresentationStages where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubicalNerve
import DHH.Cubical.FinitePresentation as FP
import DHH.StableNerve.SequenceColimit as SC
import DHH.StableNerve.FiniteCoherence as FC

-- 有限呈示对象对序列余极限的阶段因子化构造（紧致性的存在半部）。
-- 本定理只用有限生成元与有限关系，不要求目标图有限或整个预层有限。
-- 存在性仍在命题截断内；程序不为任意商点选规范代表。
-- 尚未在本模块证明 Hom 的序列余极限比较为等价：那还需要
-- 同阶段映射在余极限中相等时，于某个更晚阶段已经相等的另一半。
module Stages {ℓ : Level} (A : ℕ → CubicalSet ℓ)
              (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s
  module K = FC.Coherence A s

  module Presented (r : ℕ) (dim : Fin r → ℕ) (q : ℕ)
           (relations : Fin q → FP.Relation dim) where
    module P = FP.Presentation r dim q relations

    convertRelation : FP.Relation dim → K.Relation dim
    K.relationDimension (convertRelation e) = FP.relationDimension e
    K.leftNode (convertRelation e) = FP.leftNode e
    K.rightNode (convertRelation e) = FP.rightNode e
    K.leftMap (convertRelation e) = FP.leftMap e
    K.rightMap (convertRelation e) = FP.rightMap e

    record StageFactorization (h : CubicalNatural P.complex C.colimitCubical) : Type ℓ where
      field
        stage : ℕ
        stageMap : CubicalNatural P.complex (A stage)
        recovers : stageMap ⋆n C.include stage ≡ h
    open StageFactorization public

    -- DiagramLift给出整个有限关系列表在同阶段成立；finitePresentation
    -- 的降商泛性质将这份证书扩展成全部维数上的自然变换。
    fromDiagram : (h : CubicalNatural P.complex C.colimitCubical)
      → K.DiagramLift r dim (P.extractNodes C.colimitCubical h) q
          (λ e → convertRelation (relations e))
      → StageFactorization h
    stage (fromDiagram h d) = K.stage d
    stageMap (fromDiagram h d) = P.Interpret.factor
      (A (K.stage d)) (K.stageCells d) (K.relationsHold d)
    recovers (fromDiagram h d) =
      P.Interpret.factor-unique C.colimitCubical
        (P.extractNodes C.colimitCubical h) (P.extractRelations C.colimitCubical h)
        (stageMap (fromDiagram h d) ⋆n C.include (K.stage d))
        (λ i → cong (mapCells (C.include (K.stage d)) (dim i))
          (P.Interpret.factor-on-node (A (K.stage d)) (K.stageCells d) (K.relationsHold d) i)
          ∙ K.represents d i)
      ∙ sym (P.Interpret.factor-unique C.colimitCubical
          (P.extractNodes C.colimitCubical h) (P.extractRelations C.colimitCubical h)
          h (λ i → refl))

    factorThroughStage : (h : CubicalNatural P.complex C.colimitCubical)
      → ∥ StageFactorization h ∥₁
    factorThroughStage h = PT.map (fromDiagram h)
      (K.finiteDiagramLift r dim (P.extractNodes C.colimitCubical h) q
        (λ e → convertRelation (relations e)) (P.extractRelations C.colimitCubical h))

    -- 并非条件式“假如whole horn能提升则...”：给定一个实际有限
    -- 呈示及其任意全预层映射，以上函数确实返回同阶段因子化的截断证据。
    -- 应用到实际 OpenBox/Boundary 的比较与全映射提升在
    -- SelectedFinitePresentation / WholeBoxStages 中逐层完成。
