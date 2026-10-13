{-# OPTIONS --cubical --safe #-}

module DHH.Cubical.Kan where

-- 研究视角：填充问题的输入不只是维数，而是带相容边界的数据。
-- 想用递归证明 Kan 性，需先给出递归生成 fillingCell 的规则，再证明
-- 每个已有面被保持；单有维数递归或边界的粘合定理都不提供这个规则。
-- ChosenKanFillings 将“程序 + 边界正确性”打包，便于单独研究其构造；
-- IsKan 保留仅需截断存在性的数学目标，不强加统一选择算法。

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Faces

private variable ℓ ℓ' : Level

-- 数学对象不是内建 Agda I 上的 Kan composition。这里要求填充
-- 前一模块具体构造的“少一面”子预层；这是研究图的稳定 nerve 所需的性质。
-- 用 Yoneda 以一个 (n+1)-cell 表示整个立方体映射，节省重复自然性数据。
record OpenBoxExtension {n : ℕ} (A : CubicalSet ℓ) (missing : Facet n)
  (box : CubicalNatural (OpenBox missing) A) : Type ℓ where
  field
    fillingCell : Cell A (suc n)
    fillsBox : openBoxInclusion missing ⋆n classifyCube A fillingCell ≡ box
open OpenBoxExtension public

-- 普通 Kan 性只断言每个填充存在；它未指定可执行的选择算法。
IsKan : CubicalSet ℓ → Type ℓ
IsKan A = (n : ℕ) (missing : Facet n)
  (box : CubicalNatural (OpenBox missing) A) → ∥ OpenBoxExtension A missing box ∥₁

isPropIsKan : (A : CubicalSet ℓ) → isProp (IsKan A)
isPropIsKan A = isPropΠ3 (λ n missing box → squash₁)

-- 程序化研究可先尝试这个更强的数据：输入缺面与全部已有面的相容映射，
-- 输出一个 cell 和边界正确性证明。由此必得普通 Kan 性；反向不偷用选择。
record ChosenKanFillings (A : CubicalSet ℓ) : Type ℓ where
  field
    fillOpenBox : (n : ℕ) (missing : Facet n) (box : CubicalNatural (OpenBox missing) A)
      → OpenBoxExtension A missing box
open ChosenKanFillings public

chosenFillings→Kan : {A : CubicalSet ℓ} → ChosenKanFillings A → IsKan A
chosenFillings→Kan F n missing box = ∣ fillOpenBox F n missing box ∣₁

-- 纤维化的填充还需保持一个已经指定的目标 cell。
-- 所有等式都涉及实际预层映射，不把“边界相容”当作未定义的口头条件。
record LiftingProblem {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
  (p : CubicalNatural A B) {n : ℕ} (missing : Facet n) : Type (ℓ-max ℓ ℓ') where
  field
    top : CubicalNatural (OpenBox missing) A
    bottom : Cell B (suc n)
    squareCommutes : top ⋆n p ≡ openBoxInclusion missing ⋆n classifyCube B bottom
open LiftingProblem public

record BoxLift {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
  (p : CubicalNatural A B) {n : ℕ} {missing : Facet n}
  (problem : LiftingProblem p missing) : Type (ℓ-max ℓ ℓ') where
  field
    sourceCell : Cell A (suc n)
    extendsTop : openBoxInclusion missing ⋆n classifyCube A sourceCell ≡ top problem
    projectsToBottom : mapCells p (suc n) sourceCell ≡ bottom problem
open BoxLift public

IsKanFibration : {A : CubicalSet ℓ} {B : CubicalSet ℓ'} → CubicalNatural A B
  → Type (ℓ-max ℓ ℓ')
IsKanFibration p = (n : ℕ) (missing : Facet n) (problem : LiftingProblem p missing)
  → ∥ BoxLift p problem ∥₁

isPropIsKanFibration : {A : CubicalSet ℓ} {B : CubicalSet ℓ'} (p : CubicalNatural A B)
  → isProp (IsKanFibration p)
isPropIsKanFibration p = isPropΠ3 (λ n missing problem → squash₁)

-- 可执行的基本检查：恒等映射的提升直接使用已给出的 bottom cell。
-- 这里确实构造提升及两条方程，不是把纤维化仅声明为接口。
identityLift : (A : CubicalSet ℓ) {n : ℕ} {missing : Facet n}
  (problem : LiftingProblem (cubicalId A) missing) → BoxLift (cubicalId A) problem
sourceCell (identityLift A problem) = bottom problem
extendsTop (identityLift A problem) = sym (squareCommutes problem)
  ∙ cubicalNaturalExt (λ m u → refl)
projectsToBottom (identityLift A problem) = refl

identityKanFibration : (A : CubicalSet ℓ) → IsKanFibration (cubicalId A)
identityKanFibration A n missing problem = ∣ identityLift A problem ∣₁

-- 下一步需要对 N∞ 真正生成填充并证明边界正确；以上定义和恒等例子
-- 都不提供这个结论。有限阶段数据的共同提升，是可能用到的递归基础。
