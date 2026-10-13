{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Quasicategories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Horns

private variable ℓ : Level

-- 保持数值不变的有限序数嵌入；结构递归只处理零/后继。
weakenIndex : {n : ℕ} → Fin n → Fin (suc n)
weakenIndex fzero = fzero
weakenIndex (fsuc i) = fsuc (weakenIndex i)

-- (n+1)-单纯形的内部面恰好为1,...,n；n=0时无输入，
-- 因而准范畴条件不会要求任意两个点之间都有一条边。
innerFacet : {n : ℕ} → Fin n → Facet n
innerFacet i = fsuc (weakenIndex i)

record HornExtension (A : SimplicialSet ℓ) {n : ℕ} (missing : Facet n)
                     (horn : SimplicialNatural (Horn missing) A) : Type ℓ where
  field
    simplex : SCell A (suc n)
    restrictsToHorn : hornInclusion missing ⋆s classifySimplex A simplex ≡ horn
open HornExtension public

IsQuasicategory : SimplicialSet ℓ → Type ℓ
IsQuasicategory A = (n : ℕ) (i : Fin n)
  (horn : SimplicialNatural (Horn (innerFacet i)) A)
  → ∥ HornExtension A (innerFacet i) horn ∥₁

isPropIsQuasicategory : (A : SimplicialSet ℓ) → isProp (IsQuasicategory A)
isPropIsQuasicategory A = isPropΠ3 (λ n i horn → squash₁)

IsSimplicialKan : SimplicialSet ℓ → Type ℓ
IsSimplicialKan A = (n : ℕ) (i : Facet n)
  (horn : SimplicialNatural (Horn i) A) → ∥ HornExtension A i horn ∥₁

kan→quasicategory : {A : SimplicialSet ℓ} → IsSimplicialKan A → IsQuasicategory A
kan→quasicategory kan n i = kan n (innerFacet i)

-- 指定填充程序比截断存在更强。定义准范畴不意味着已经给出了
-- 原文 N□Graph 的内角填充证明；其所需局部 Kan 性是另一项实际义务。
record ChosenInnerFillings (A : SimplicialSet ℓ) : Type ℓ where
  field
    fillInner : (n : ℕ) (i : Fin n)
      (horn : SimplicialNatural (Horn (innerFacet i)) A)
      → HornExtension A (innerFacet i) horn

chosenInner→quasicategory : {A : SimplicialSet ℓ}
  → ChosenInnerFillings A → IsQuasicategory A
chosenInner→quasicategory chosen n i horn =
  ∣ ChosenInnerFillings.fillInner chosen n i horn ∣₁
