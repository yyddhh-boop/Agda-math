{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.PresentationComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Functions.Embedding using (injEmbedding)
open import Cubical.Functions.Surjection using (isSurjection; isEmbedding×isSurjection→isEquiv)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubicalNerve
import DHH.Cubical.FinitePresentation as FP
import DHH.StableNerve.SequenceColimit as SC
import DHH.StableNerve.CommonStage as CS
import DHH.StableNerve.PresentationStages as PS
import DHH.StableNerve.PresentationEqualities as PE

-- 实际比较：阶段映射按“在某个共同后阶段相等”取商，等价于
-- 从有限呈示到目标序列余极限的全预层映射集合。两个方向的
-- 实质工作分别是有限关系的同步，以及有限生成元等式的同步。
module Comparison {ℓ : Level} (A : ℕ → CubicalSet ℓ)
  (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s
  module K = CS.CommonStages A s
  module Stages = PS.Stages A s
  module Equalities = PE.Equalities A s

  module Presented (r : ℕ) (dim : Fin r → ℕ) (q : ℕ)
    (relations : Fin q → FP.Relation dim) where
    module P = FP.Presentation r dim q relations
    module S = Stages.Presented r dim q relations
    module E = Equalities.Presented r dim q relations

    Tagged : Type ℓ
    Tagged = Σ[ k ∈ ℕ ] CubicalNatural P.complex (A k)

    Eventually : Tagged → Tagged → Type ℓ
    Eventually x y = ∥ E.LaterEquality (snd x) (snd y) ∥₁

    StageMaps : Type ℓ
    StageMaps = Tagged SQ./ Eventually

    compareTagged : Tagged → CubicalNatural P.complex C.colimitCubical
    compareTagged (k , h) = h ⋆n C.include k

    eventuallySound : (x y : Tagged) → Eventually x y → compareTagged x ≡ compareTagged y
    eventuallySound (k , h) (l , g) = PT.rec (isSetCubicalNatural _ _) λ w →
      cubicalNaturalExt
        {A = P.complex} {B = C.colimitCubical}
        {f = compareTagged (k , h)} {g = compareTagged (l , g)}
        (λ n c → K.point-advance (E.leftBound w) n (mapCells h n c)
          ∙ cong (λ f → mapCells (C.include (E.stage w)) n (mapCells f n c)) (E.mapsAgree w)
          ∙ sym (K.point-advance (E.rightBound w) n (mapCells g n c)))

    comparison : StageMaps → CubicalNatural P.complex C.colimitCubical
    comparison = SQ.rec isSetCubicalNatural compareTagged eventuallySound

    comparison-surjective : isSurjection comparison
    comparison-surjective h = PT.map
      (λ d → SQ.[ S.stage d , S.stageMap d ] , S.recovers d)
      (S.factorThroughStage h)

    comparison-injective : (x y : StageMaps) → comparison x ≡ comparison y → x ≡ y
    comparison-injective = SQ.elimProp2
      (λ x y → isPropΠ (λ _ → SQ.squash/ x y))
      (λ x y e → SQ.eq/ x y (E.equalAtLater (snd x) (snd y) e))

    finitePresentationComparison : StageMaps ≃ CubicalNatural P.complex C.colimitCubical
    finitePresentationComparison = comparison , isEmbedding×isSurjection→isEquiv
      (injEmbedding isSetCubicalNatural (λ {x} {y} → comparison-injective x y)
        , comparison-surjective)

-- 范围是这个明确的共同后阶段商与实际序列预层余极限。
-- 未在此提供任意 filtered category 的余极限定理；也没有得到
-- 可判定的相等搜索、规范代表、无限选择或图的 Kan 填充。
