{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.StableStages where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.CommonStage
open import DHH.StableNerve.FiniteStages

-- 将一般序列的定理用到实际交替网格序列，不再把过渡映射作为任意参数。
-- k 是阶段编号，网格边长为 k+1；维数 n 与阶段 k 是不同的递归参数。
module ForGraph {ℓ : Level} (G : Graph ℓ) where
  module K = CommonStages (Stage G) (stageTransition G)
  module F = FiniteFamilies (Stage G) (stageTransition G)

  -- 余极限中的两份网格数据相等，当且仅当在某个共同后阶段相等。
  -- Common 包含命题截断：从抽象等式不会自动得到可执行的阶段搜索。
  stableEquality : (n k l : ℕ)
    (c : Hom (Grid (suc k) n) G) (d : Hom (Grid (suc l) n) G)
    → (mapCells (includeStage G k) n c ≡ mapCells (includeStage G l) n d)
      ≃ K.Common n (k , c) (l , d)
  stableEquality n k l c d = K.equalityCommonEquivalence n (k , c) (l , d)

  -- 输入每一项的有限网格和阶段，程序递归取阶段 max，逐项过渡。
  -- 返回一个真正的共同阶段、该阶段的图映射，以及表示原 cell 的证书。
  moveFiniteGrids : (n r : ℕ)
    (xs : Fin r → Σ[ k ∈ ℕ ] Hom (Grid (suc k) n) G)
    → Σ[ M ∈ ℕ ] Σ[ cs ∈ (Fin r → Hom (Grid (suc M) n) G) ]
      ((i : Fin r) → mapCells (includeStage G M) n (cs i)
        ≡ mapCells (includeStage G (fst (xs i))) n (snd (xs i)))
  moveFiniteGrids = F.finiteTaggedRepresentatives

  -- 仅给 N∞ 中的有限族，则得到截断的共同阶段表示。有限递归消去截断
  -- 不需要可数选择，但其输出也没有成为未截断的规范表示。
  finiteStableCells : (n r : ℕ) (xs : Fin r → Cell (N∞ G) n)
    → ∥ Σ[ M ∈ ℕ ] Σ[ cs ∈ (Fin r → Hom (Grid (suc M) n) G) ]
        ((i : Fin r) → mapCells (includeStage G M) n (cs i) ≡ xs i) ∥₁
  finiteStableCells = F.finiteRepresentatives

  -- 研究接口：已解决的是固定维数的有限族表示；尚未证明有限边界图式
  -- 的所有相容等式能同时提升，也未由此给出 open-box 的填充。
  -- 下一步需要把相等的阶段见证一同合并，再研究保边的填充规则。
