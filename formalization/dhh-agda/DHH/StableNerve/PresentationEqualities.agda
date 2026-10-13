{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.PresentationEqualities where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubicalNerve
import DHH.Cubical.FinitePresentation as FP
import DHH.StableNerve.SequenceColimit as SC
import DHH.StableNerve.CommonStage as CS
import DHH.StableNerve.FiniteCoherence as FC

-- 阶段因子化之外的另一半：余极限中的全映射等式能在更晚阶段
-- 成立。同步的有限输入是生成元上的等式；预层的泛性质随后把
-- 它们扩展到全部维数。无需枚举无限的高维 cell 或搜索无限阶段。
module Equalities {ℓ : Level} (A : ℕ → CubicalSet ℓ)
  (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s
  module K = CS.CommonStages A s
  module F = FC.Coherence A s

  module Presented (r : ℕ) (dim : Fin r → ℕ) (q : ℕ)
    (relations : Fin q → FP.Relation dim) where
    module P = FP.Presentation r dim q relations

    record LaterEquality {k l : ℕ}
      (h : CubicalNatural P.complex (A k))
      (g : CubicalNatural P.complex (A l)) : Type ℓ where
      field
        stage : ℕ
        leftBound : k ≤ stage
        rightBound : l ≤ stage
        mapsAgree : h ⋆n K.advance leftBound ≡ g ⋆n K.advance rightBound
    open LaterEquality public

    leftTags : {k : ℕ} (h : CubicalNatural P.complex (A k))
      → (i : Fin r) → C.Tagged (dim i)
    leftTags {k} h i = k , mapCells h (dim i) (P.nodeCell i)

    fromSynchronized : {k l : ℕ}
      (h : CubicalNatural P.complex (A k))
      (g : CubicalNatural P.complex (A l))
      → F.SimultaneousWitness r dim (leftTags h) (leftTags g) → LaterEquality h g
    fromSynchronized {k} {l} h g w = result
      where
      -- 显式保留两个原阶段作为 max 的输入，覆盖 r=0 空呈示。
      -- 空输入同步器返回 0，但这不保证 k,l≤0。
      M = max (max k l) (fst w)
      p : k ≤ M
      p = ≤-trans (left-≤-max {m = k} {n = l})
        (left-≤-max {m = max k l} {n = fst w})
      v : l ≤ M
      v = ≤-trans (right-≤-max {n = l} {m = k})
        (left-≤-max {m = max k l} {n = fst w})
      raised : (i : Fin r) → K.Witness (dim i) (leftTags h i) (leftTags g i)
      raised i = K.raiseWitness
        (fst w , fst (snd w) i , fst (snd (snd w)) i , snd (snd (snd w)) i)
        {L = M} (right-≤-max {n = fst w} {m = max k l})

      H : CubicalNatural P.complex (A M)
      H = h ⋆n K.advance p
      G : CubicalNatural P.complex (A M)
      G = g ⋆n K.advance v
      nodesAgree : (i : Fin r) → mapCells H (dim i) (P.nodeCell i)
        ≡ mapCells G (dim i) (P.nodeCell i)
      nodesAgree i =
        K.advanceCell-proof-irrelevant p (fst (snd (raised i))) (dim i)
          (mapCells h (dim i) (P.nodeCell i))
        ∙ snd (snd (snd (raised i)))
        ∙ K.advanceCell-proof-irrelevant (fst (snd (snd (raised i)))) v (dim i)
          (mapCells g (dim i) (P.nodeCell i))

      module I = P.Interpret (A M) (P.extractNodes (A M) G) (P.extractRelations (A M) G)
      result : LaterEquality h g
      stage result = M
      leftBound result = p
      rightBound result = v
      mapsAgree result = I.factor-unique H nodesAgree
        ∙ sym (I.factor-unique G (λ i → refl))

    equalAtLater : {k l : ℕ}
      (h : CubicalNatural P.complex (A k))
      (g : CubicalNatural P.complex (A l))
      → h ⋆n C.include k ≡ g ⋆n C.include l → ∥ LaterEquality h g ∥₁
    equalAtLater h g e = PT.map (fromSynchronized h g)
      (F.synchronizeEqualities r dim (leftTags h) (leftTags g)
        (λ i → cong (λ f → mapCells f (dim i) (P.nodeCell i)) e))

-- 和 PresentationStages.factorThroughStage 合起来，这提供了有限
-- 呈示对序列余极限比较的两个实质步骤。Hom 商的等价打包与一般
-- filtered diagram 的版本仍是进一步构造，不能由此偷换成已完成。
