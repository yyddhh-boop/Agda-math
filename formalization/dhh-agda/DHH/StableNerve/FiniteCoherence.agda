{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.FiniteCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubeCategory
open import DHH.CubicalNerve
import DHH.StableNerve.CommonStage as CS
import DHH.StableNerve.FiniteStages as FS
import DHH.StableNerve.SequenceColimit as SC

private variable ℓ : Level

-- 结构递归只依赖有限索引的长度。每一步消去两个命题截断，结果仍在
-- 命题截断内；这里没有从商选规范代表，也没有使用可数选择。
finiteChoice : (r : ℕ) (P : Fin r → Type ℓ)
  → ((i : Fin r) → ∥ P i ∥₁) → ∥ ((i : Fin r) → P i) ∥₁
finiteChoice zero P w = ∣ (λ ()) ∣₁
finiteChoice (suc r) P w = PT.rec2 squash₁
  (λ head tail → ∣ (λ where
    fzero → head
    (fsuc i) → tail i) ∣₁)
  (w fzero) (finiteChoice r (λ i → P (fsuc i)) (λ i → w (fsuc i)))

-- 上界的输入只有自然数；因此同一有限族的各项可以有不同维数。
finiteNatBound : (r : ℕ) (ks : Fin r → ℕ)
  → Σ[ M ∈ ℕ ] ((i : Fin r) → ks i ≤ M)
finiteNatBound zero ks = zero , (λ ())
finiteNatBound (suc r) ks =
  let tail = finiteNatBound r (λ i → ks (fsuc i))
  in max (ks fzero) (fst tail) , λ where
    fzero → left-≤-max
    (fsuc i) → ≤-trans (snd tail i) right-≤-max

module Coherence (A : ℕ → CubicalSet ℓ)
                 (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where
  module C = SC.Colimit A s
  module K = CS.CommonStages A s
  module F = FS.FiniteFamilies A s

  HeterogeneousRepresentation : (r : ℕ) (dim : Fin r → ℕ)
    → ((i : Fin r) → C.Points (dim i)) → Type ℓ
  HeterogeneousRepresentation r dim xs = Σ[ M ∈ ℕ ]
    Σ[ cs ∈ ((i : Fin r) → Cell (A M) (dim i)) ]
      ((i : Fin r) → C.point (dim i) (M , cs i) ≡ xs i)

  heterogeneousTaggedRepresentatives : (r : ℕ) (dim : Fin r → ℕ)
    (xs : (i : Fin r) → C.Tagged (dim i))
    → HeterogeneousRepresentation r dim (λ i → C.point (dim i) (xs i))
  heterogeneousTaggedRepresentatives r dim xs =
    let bound = finiteNatBound r (λ i → fst (xs i))
        cs = λ i → K.advanceCell (snd bound i) (dim i) (snd (xs i))
    in fst bound , cs , λ i → sym (K.point-advance (snd bound i) (dim i) (snd (xs i)))

  heterogeneousRepresentatives : (r : ℕ) (dim : Fin r → ℕ)
    (xs : (i : Fin r) → C.Points (dim i))
    → ∥ HeterogeneousRepresentation r dim xs ∥₁
  heterogeneousRepresentatives r dim xs = PT.map
    (λ reps →
      let tags = λ i → fst (reps i) , fst (snd (reps i))
          lifted = heterogeneousTaggedRepresentatives r dim tags
      in fst lifted , fst (snd lifted) ,
        λ i → snd (snd lifted) i ∙ snd (snd (reps i)))
    (finiteChoice r
      (λ i → Σ[ k ∈ ℕ ] Σ[ c ∈ Cell (A k) (dim i) ] C.point (dim i) (k , c) ≡ xs i)
      (λ i → F.pointRepresentative (dim i) (xs i)))

  -- 最小同步定理：关系本身也有维数标签。每条关系的显式见证先给出
  -- 一个阶段，再取这些阶段的 max；raiseWitness 保持原等式。
  SimultaneousWitness : (r : ℕ) (dim : Fin r → ℕ)
    (xs ys : (i : Fin r) → C.Tagged (dim i)) → Type ℓ
  SimultaneousWitness r dim xs ys = Σ[ M ∈ ℕ ]
    Σ[ ps ∈ ((i : Fin r) → fst (xs i) ≤ M) ]
    Σ[ qs ∈ ((i : Fin r) → fst (ys i) ≤ M) ]
      ((i : Fin r) → K.advanceCell (ps i) (dim i) (snd (xs i))
        ≡ K.advanceCell (qs i) (dim i) (snd (ys i)))

  synchronizeWitnesses : (r : ℕ) (dim : Fin r → ℕ)
    (xs ys : (i : Fin r) → C.Tagged (dim i))
    → ((i : Fin r) → K.Witness (dim i) (xs i) (ys i))
    → SimultaneousWitness r dim xs ys
  synchronizeWitnesses r dim xs ys ws =
    let bound = finiteNatBound r (λ i → fst (ws i))
        raised : (i : Fin r) → K.Witness (dim i) (xs i) (ys i)
        raised = λ i → K.raiseWitness (ws i) (snd bound i)
    in fst bound , (λ i → fst (snd (raised i))) ,
      (λ i → fst (snd (snd (raised i)))) ,
      (λ i → snd (snd (snd (raised i))))

  synchronizeEqualities : (r : ℕ) (dim : Fin r → ℕ)
    (xs ys : (i : Fin r) → C.Tagged (dim i))
    → ((i : Fin r) → C.point (dim i) (xs i) ≡ C.point (dim i) (ys i))
    → ∥ SimultaneousWitness r dim xs ys ∥₁
  synchronizeEqualities r dim xs ys eq = PT.map
    (synchronizeWitnesses r dim xs ys)
    (finiteChoice r (λ i → K.Witness (dim i) (xs i) (ys i))
      (λ i → K.equality-to-common (dim i) (xs i) (ys i) (eq i)))

  -- 有限图式：节点有各自维数；每条关系把两个节点重索引到同一维数。
  -- 包括通常的面相容式，也允许任意已给出的 CubicalMap（退化/联结等）。
  -- 关系列表仍须有限；没有暗中量化所有高维重索引的相交。
  record Relation {r : ℕ} (dim : Fin r → ℕ) : Type₀ where
    field
      relationDimension : ℕ
      leftNode rightNode : Fin r
      leftMap : CubicalMap relationDimension (dim leftNode)
      rightMap : CubicalMap relationDimension (dim rightNode)
  open Relation public

  Equation : {r : ℕ} {dim : Fin r → ℕ} (B : CubicalSet ℓ)
    (xs : (i : Fin r) → Cell B (dim i)) → Relation dim → Type ℓ
  Equation B xs e = reindex B (leftMap e) (xs (leftNode e))
    ≡ reindex B (rightMap e) (xs (rightNode e))

  LeftTagged RightTagged : {r : ℕ} {dim : Fin r → ℕ}
    (xs : (i : Fin r) → C.Tagged (dim i)) (e : Relation dim)
    → C.Tagged (relationDimension e)
  LeftTagged xs e = C.actTagged (leftMap e) (xs (leftNode e))
  RightTagged xs e = C.actTagged (rightMap e) (xs (rightNode e))

  record DiagramLift (r : ℕ) (dim : Fin r → ℕ)
    (xs : (i : Fin r) → C.Points (dim i)) (q : ℕ)
    (relations : Fin q → Relation dim) : Type ℓ where
    field
      stage : ℕ
      stageCells : (i : Fin r) → Cell (A stage) (dim i)
      represents : (i : Fin r) → C.point (dim i) (stage , stageCells i) ≡ xs i
      relationsHold : (j : Fin q) → Equation (A stage) stageCells (relations j)
  open DiagramLift public

  -- 显式构造的两组有限输入：所有节点的阶段，以及所有关系的见证阶段。
  -- 合并上界后用 advance 的自然性把“先重索引再过渡”的等式换成
  -- “先把所有节点过渡到共同阶段，再重索引”的图式相容式。
  liftTaggedWithWitnesses : (r : ℕ) (dim : Fin r → ℕ)
    (xs : (i : Fin r) → C.Tagged (dim i)) (q : ℕ)
    (relations : Fin q → Relation dim)
    → ((j : Fin q) → K.Witness (relationDimension (relations j))
        (LeftTagged xs (relations j)) (RightTagged xs (relations j)))
    → DiagramLift r dim (λ i → C.point (dim i) (xs i)) q relations
  liftTaggedWithWitnesses r dim xs q relations witnesses = result
    where
    nodeBound = finiteNatBound r (λ i → fst (xs i))
    relationBound = finiteNatBound q (λ j → fst (witnesses j))
    M = max (fst nodeBound) (fst relationBound)
    ps : (i : Fin r) → fst (xs i) ≤ M
    ps i = ≤-trans (snd nodeBound i) left-≤-max
    cs : (i : Fin r) → Cell (A M) (dim i)
    cs i = K.advanceCell (ps i) (dim i) (snd (xs i))
    raised : (j : Fin q) → K.Witness (relationDimension (relations j))
      (LeftTagged xs (relations j)) (RightTagged xs (relations j))
    raised j = K.raiseWitness (witnesses j)
      (≤-trans (snd relationBound j) (right-≤-max {m = fst nodeBound}))
    equalAtStage : (j : Fin q) → Equation (A M) cs (relations j)
    equalAtStage j =
      let e = relations j
          l = leftNode e
          t = rightNode e
          w = raised j
          p = fst (snd w)
          v = fst (snd (snd w))
          eq = snd (snd (snd w))
          n = relationDimension e
      in sym (natural (K.advance (ps l)) (leftMap e) (snd (xs l)))
        ∙ K.advanceCell-proof-irrelevant (ps l) p n
          (reindex (A (fst (xs l))) (leftMap e) (snd (xs l)))
        ∙ eq
        ∙ K.advanceCell-proof-irrelevant v (ps t) n
          (reindex (A (fst (xs t))) (rightMap e) (snd (xs t)))
        ∙ natural (K.advance (ps t)) (rightMap e) (snd (xs t))
    result : DiagramLift r dim (λ i → C.point (dim i) (xs i)) q relations
    stage result = M
    stageCells result = cs
    represents result i = sym (K.point-advance (ps i) (dim i) (snd (xs i)))
    relationsHold result = equalAtStage

  liftTaggedEqualities : (r : ℕ) (dim : Fin r → ℕ)
    (xs : (i : Fin r) → C.Tagged (dim i)) (q : ℕ)
    (relations : Fin q → Relation dim)
    → ((j : Fin q) → Equation C.colimitCubical
        (λ i → C.point (dim i) (xs i)) (relations j))
    → ∥ DiagramLift r dim (λ i → C.point (dim i) (xs i)) q relations ∥₁
  liftTaggedEqualities r dim xs q relations eq = PT.map
    (liftTaggedWithWitnesses r dim xs q relations)
    (finiteChoice q
      (λ j → K.Witness (relationDimension (relations j))
        (LeftTagged xs (relations j)) (RightTagged xs (relations j)))
      (λ j → K.equality-to-common (relationDimension (relations j))
        (LeftTagged xs (relations j)) (RightTagged xs (relations j)) (eq j)))

  -- 任意 colimit cells 的版本再消去一次有限族的表示截断。
  -- 最终仍是截断存在，但返回对象内部确实带有同阶段的全部相容等式。
  finiteDiagramLift : (r : ℕ) (dim : Fin r → ℕ)
    (xs : (i : Fin r) → C.Points (dim i)) (q : ℕ)
    (relations : Fin q → Relation dim)
    → ((j : Fin q) → Equation C.colimitCubical xs (relations j))
    → ∥ DiagramLift r dim xs q relations ∥₁
  finiteDiagramLift r dim xs q relations eq = PT.rec squash₁
    (λ { (L , cs , represents-xs) →
      let tags = λ i → L , cs i
          relation-eq : (j : Fin q) → Equation C.colimitCubical
            (λ i → C.point (dim i) (tags i)) (relations j)
          relation-eq j =
            let e = relations j
            in cong (reindex C.colimitCubical (leftMap e)) (represents-xs (leftNode e))
              ∙ eq j
              ∙ cong (reindex C.colimitCubical (rightMap e)) (sym (represents-xs (rightNode e)))
          changeRepresentation : DiagramLift r dim
            (λ i → C.point (dim i) (tags i)) q relations → DiagramLift r dim xs q relations
          changeRepresentation d = record
            { stage = stage d
            ; stageCells = stageCells d
            ; represents = λ i → represents d i ∙ represents-xs i
            ; relationsHold = relationsHold d }
      in PT.map changeRepresentation (liftTaggedEqualities r dim tags q relations relation-eq) })
    (heterogeneousRepresentatives r dim xs)

  -- 范围：本模块同步给定的有限异维节点与有限重索引关系列表。
  -- FaceIntersections / SelectedFinitePresentation 将实际选面复形的
  -- 全部相交归约到有限呈示；WholeBoxStages 随后证明整个 OpenBox
  -- 的阶段因子化。这里仍没有假定或证明内部 Kan 填充。
