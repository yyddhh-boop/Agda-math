{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Equivalences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Quasicategories
open import DHH.Simplicial.WalkingIsomorphism
open import DHH.Simplicial.Products

private variable ℓ ℓ' : Level

-- 原论文 Definition 2.7 的 E¹-homotopy equivalence 数据。
-- WalkingIso 是该 E¹（不是原文另一个有限参数对象 J）。
-- 将“逆函子存在”截断，避免把定理的命题读成自动选择逆函子的程序。
record IsoHomotopyInverse {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                         (f : SimplicialNatural A B) : Type (ℓ-max ℓ ℓ') where
  field
    inverse : SimplicialNatural B A
    sourceInverse : IsoHomotopy (f ⋆s inverse) (simplicialId A)
    targetInverse : IsoHomotopy (inverse ⋆s f) (simplicialId B)
open IsoHomotopyInverse public

IsIsoHomotopyEquivalence : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  → SimplicialNatural A B → Type (ℓ-max ℓ ℓ')
IsIsoHomotopyEquivalence f = ∥ IsoHomotopyInverse f ∥₁

isPropIsIsoHomotopyEquivalence : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  (f : SimplicialNatural A B) → isProp (IsIsoHomotopyEquivalence f)
isPropIsIsoHomotopyEquivalence f = squash₁

-- 把两个准范畴条件显式保留，不能用一般单纯集合的空间弱等价替代。
record EquivalenceOfQuasicategories {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                                   (f : SimplicialNatural A B)
                                   : Type (ℓ-max ℓ ℓ') where
  field
    sourceQuasicategory : IsQuasicategory A
    targetQuasicategory : IsQuasicategory B
    equivalence : IsIsoHomotopyEquivalence f
open EquivalenceOfQuasicategories public

equivalenceOfQuasicategories-isProp : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  (f : SimplicialNatural A B) → isProp (EquivalenceOfQuasicategories f)
sourceQuasicategory (equivalenceOfQuasicategories-isProp {A = A} f p q i) =
  isPropIsQuasicategory A (sourceQuasicategory p) (sourceQuasicategory q) i
targetQuasicategory (equivalenceOfQuasicategories-isProp {B = B} f p q i) =
  isPropIsQuasicategory B (targetQuasicategory p) (targetQuasicategory q) i
equivalence (equivalenceOfQuasicategories-isProp f p q i) =
  squash₁ (equivalence p) (equivalence q) i

identityInverse : (A : SimplicialSet ℓ) → IsoHomotopyInverse (simplicialId A)
inverse (identityInverse A) = simplicialId A
homotopy (sourceInverse (identityInverse A)) = firstS {A = A} {B = WalkingIso}
atFalse (sourceInverse (identityInverse A)) = simplicialNaturalExt (λ _ _ → refl)
atTrue (sourceInverse (identityInverse A)) = simplicialNaturalExt (λ _ _ → refl)
homotopy (targetInverse (identityInverse A)) = firstS {A = A} {B = WalkingIso}
atFalse (targetInverse (identityInverse A)) = simplicialNaturalExt (λ _ _ → refl)
atTrue (targetInverse (identityInverse A)) = simplicialNaturalExt (λ _ _ → refl)

identityEquivalence : (A : SimplicialSet ℓ) → IsQuasicategory A
  → EquivalenceOfQuasicategories (simplicialId A)
sourceQuasicategory (identityEquivalence A q) = q
targetQuasicategory (identityEquivalence A q) = q
equivalence (identityEquivalence A q) = ∣ identityInverse A ∣₁

-- 此处给出原猜想结论可以使用的具体 type；没有构造原图 nerve、
-- 原 marked Ex 或候选模型的比较，因而不能单独视作完整原论文 DHH。
