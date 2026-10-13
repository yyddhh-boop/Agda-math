{-# OPTIONS --cubical --safe #-}

module DHH.Cubical.KanComposition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.Kan

private variable ℓA ℓB ℓC : Level

module Composition {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC}
  (p : CubicalNatural A B) (q : CubicalNatural B C)
  {n : ℕ} {missing : Facet n}
  (problem : LiftingProblem (p ⋆n q) missing) where

  -- 一次具体提升分成两步，不枚举候选填充。
  -- 原问题：OpenBox --top--> A --p--> B --q--> C
  --         |                               ↑ bottom
  --         Cube ---------------------------+
  -- 第一步把顶边送到 B，以原 bottom 为底边，沿 q 提升。
  outerProblem : LiftingProblem q missing
  top outerProblem = top problem ⋆n p
  bottom outerProblem = bottom problem
  squareCommutes outerProblem = cubicalNaturalExt (λ m c → refl)
    ∙ squareCommutes problem

  -- 第一步的填充 b 已有“边界是 top 后接 p”的证书。
  -- 因而 b 正好作为第二个交换方块的底边，可以沿 p 提升。
  innerProblem : BoxLift q outerProblem → LiftingProblem p missing
  top (innerProblem outerLift) = top problem
  bottom (innerProblem outerLift) = sourceCell outerLift
  squareCommutes (innerProblem outerLift) = sym (extendsTop outerLift)

  -- 给定两份实际填充数据，直接输出复合映射的填充。
  -- sourceCell 沿用第二次填充；边界证书沿用其 extendsTop；
  -- 投影证书由 p(a)=b 与 q(b)=bottom 作等式拼接得到。
  pasteLift : (outerLift : BoxLift q outerProblem)
    → BoxLift p (innerProblem outerLift) → BoxLift (p ⋆n q) problem
  sourceCell (pasteLift outerLift innerLift) = sourceCell innerLift
  extendsTop (pasteLift outerLift innerLift) = extendsTop innerLift
  projectsToBottom (pasteLift outerLift innerLift) =
    cong (mapCells q (suc n)) (projectsToBottom innerLift)
    ∙ projectsToBottom outerLift

-- 普通纤维化只提供截断存在。两次 PT.rec 都消去到“复合提升存在”
-- 这个命题中，故不会从截断存在抽出全局填充选择函数。
-- 上面的 pasteLift 是实际构造步骤；这里仅把它推广到存在性的陈述。
composeKanFibrations : {A : CubicalSet ℓA} {B : CubicalSet ℓB} {C : CubicalSet ℓC}
  (p : CubicalNatural A B) (q : CubicalNatural B C)
  → IsKanFibration p → IsKanFibration q → IsKanFibration (p ⋆n q)
composeKanFibrations p q pFib qFib n missing problem =
  PT.rec squash₁
    (λ outerLift → PT.rec squash₁
      (λ innerLift → ∣ Steps.pasteLift outerLift innerLift ∣₁)
      (pFib n missing (Steps.innerProblem outerLift)))
    (qFib n missing Steps.outerProblem)
  where
  module Steps = Composition p q problem

-- 恒等纤维化已由 Kan.identityLift/identityKanFibration 显式构造。
-- 本文件添加的是任意维数、任意缺面上的复合封闭性；它没有给出
-- 图的稳定 nerve 的 Kan 填充，也不证明 raw-to-stable 是弱等价。
