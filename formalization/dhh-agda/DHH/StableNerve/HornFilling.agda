{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornFilling where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.Kan
open import DHH.Cubical.GraphCoend
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.HornRetraction
open import DHH.StableNerve.HornBoundary
open import DHH.StableNerve.StagePadding
open import DHH.StableNerve.UniversalHornReduction

-- 给定实际有限阶段的整个 horn 映射，程序在精确三倍网格上填充。
-- H 可以无限且处于任意 universe；收缩从不枚举其顶点或邻接。
module StageFilling {ℓ : Level} (H : Graph ℓ) (k n : ℕ) (missing : Facet n)
  (η : CubicalNatural (OpenBox missing) (Nₘ (suc k) H)) where
  module R = Retraction k n missing
  module T = R.Target H η
  module B = BoundaryProof.TargetBoundary k n missing H η

  stageFill : OpenBoxExtension (N∞ H) missing (η ⋆n includeStage H k)
  fillingCell stageFill = mapCells (includeStage H (tripleStage k)) (suc n) T.map
  fillsBox stageFill = cubicalNaturalExt λ d c →
    sym (natural (includeStage H (tripleStage k)) (fst c) T.map)
    ∙ cong (mapCells (includeStage H (tripleStage k)) d)
      (cong (λ h → mapCells h d c) B.full-boundary)
    ∙ cong (λ h → mapCells h d (mapCells η d c)) (ForGraph.middle-include H k)

-- 这次实际填入原先只有 TYPE 的通用填充接口；单位 horn 的有限
-- 阶段已给出，无需从截断中取出一个规范阶段。
universalFill : (n : ℕ) (missing : Facet n) (k : ℕ) → Universal.Fill missing k
universalFill n missing k = StageFilling.stageFill (Universal.H missing k) k n missing
  (GraphCoend.unit (suc k) (OpenBox missing))

universalHornFillings : UniversalHornFillings
universalHornFillings n missing k = ∣ universalFill n missing k ∣₁

-- 完整 horn 的有限阶段提升已在 WholeBoxStages 证明为截断存在。
-- UniversalHornReduction 合法消去该截断，故所得是普通 IsKan；
-- 不宣称对任意稳定 horn 给出 ChosenKanFillings 的选择程序。
N∞-Kan : {ℓ : Level} (G : Graph ℓ) → IsKan (N∞ G)
N∞-Kan = universalHornFillings→Kan universalHornFillings

-- 结论是这个实际交替序列余极限 nerve 的 Kan 性。它不证明
-- N₁→N∞ 弱等价、A 群识别、原 DHH 的局部化比较或 DHH 本身。
