{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Horns where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Sets

-- 一个 (n+1)-单纯形有 n+2 个面。Horn 是选中除一个面外的面生成的
-- 子预层；不是只取各维的一组图画。成员是面分解的截断存在。
-- 预合成与结合律给出全部重索引；不搜索或枚举退化单形。
Facet : ℕ → Type₀
Facet n = Fin (suc (suc n))

facetMap : {n : ℕ} → Facet n → OrdinalMap n (suc n)
facetMap = coface

FaceSelection : ℕ → Type₁
FaceSelection n = Facet n → hProp ℓ-zero

module SelectedFaces {n : ℕ} (S : FaceSelection n) where
  Factorization : {m : ℕ} → OrdinalMap m (suc n) → Type₀
  Factorization {m} u = Σ[ j ∈ Facet n ]
    (fst (S j) × (Σ[ v ∈ OrdinalMap m n ] (v ⋆o facetMap j ≡ u)))

  Contains : {m : ℕ} → OrdinalMap m (suc n) → Type₀
  Contains u = ∥ Factorization u ∥₁

  -- 对给定的分解代表做预合成。结合律把一步的构造推广到所有算子。
  restrict : {l m : ℕ} (f : OrdinalMap l m) (u : OrdinalMap m (suc n))
    → Contains u → Contains (f ⋆o u)
  restrict f u = PT.map λ { (j , selected , v , e) →
    j , selected , (f ⋆o v) ,
    (Category.⋆Assoc Delta f v (facetMap j) ∙ cong (f ⋆o_) e) }

  complex : SimplicialSet ℓ-zero
  simplexes complex m = (Σ[ u ∈ OrdinalMap m (suc n) ] Contains u) ,
    isSetΣSndProp isSetOrdinalMap (λ _ → squash₁)
  reindexS complex f (u , p) = (f ⋆o u) , restrict f u p
  reindexS-id complex (u , p) = Σ≡Prop (λ _ → squash₁) (Category.⋆IdL Delta u)
  reindexS-compose complex f g (u , p) = Σ≡Prop (λ _ → squash₁)
    (Category.⋆Assoc Delta f g u)

  inclusion : SimplicialNatural complex (RepresentableSimplex (suc n))
  mapS inclusion m = fst
  naturalS inclusion f c = refl

  inclusion-injective : {m : ℕ} (x y : SCell complex m)
    → mapS inclusion m x ≡ mapS inclusion m y → x ≡ y
  inclusion-injective x y e = Σ≡Prop (λ _ → squash₁) e

  face : (j : Facet n) → fst (S j) → SimplicialNatural (RepresentableSimplex n) complex
  mapS (face j p) m v = (v ⋆o facetMap j) , ∣ j , p , v , refl ∣₁
  naturalS (face j p) f v = Σ≡Prop (λ _ → squash₁)
    (Category.⋆Assoc Delta f v (facetMap j))

  face-inclusion : (j : Facet n) (p : fst (S j))
    → face j p ⋆s inclusion ≡ classifySimplex (RepresentableSimplex (suc n)) (facetMap j)
  face-inclusion j p = simplicialNaturalExt λ m v → refl

allFaces : (n : ℕ) → FaceSelection n
allFaces n j = Unit , isPropUnit

exceptFace : {n : ℕ} → Facet n → FaceSelection n
exceptFace missing j = (¬ (j ≡ missing)) , isPropΠ (λ _ → Empty.isProp⊥)

Boundary : (n : ℕ) → SimplicialSet ℓ-zero
Boundary n = SelectedFaces.complex (allFaces n)

Horn : {n : ℕ} → Facet n → SimplicialSet ℓ-zero
Horn missing = SelectedFaces.complex (exceptFace missing)

boundaryInclusion : (n : ℕ) → SimplicialNatural (Boundary n) (RepresentableSimplex (suc n))
boundaryInclusion n = SelectedFaces.inclusion (allFaces n)

hornInclusion : {n : ℕ} (missing : Facet n)
  → SimplicialNatural (Horn missing) (RepresentableSimplex (suc n))
hornInclusion missing = SelectedFaces.inclusion (exceptFace missing)

-- 后续研究：有限个面生成整个边界，但其相容性必须被证明。
-- 这里没有选择分解的规范代表，也没有把“缺面”自动解释为存在填充。

-- 扩大选中的面集合只需传递选择证明；底层 cube morphism 保持不变。
-- 这把“删去一个面所得的是边界的子对象”写成实际自然映射。
selectedInclusion : {n : ℕ} {S T : FaceSelection n}
  → ((j : Facet n) → fst (S j) → fst (T j))
  → SimplicialNatural (SelectedFaces.complex S) (SelectedFaces.complex T)
mapS (selectedInclusion inc) m (u , p) = u ,
  PT.map (λ { (j , selected , v , e) → j , inc j selected , v , e }) p
naturalS (selectedInclusion inc) f (u , p) = Σ≡Prop (λ _ → squash₁) refl

hornToBoundary : {n : ℕ} (missing : Facet n)
  → SimplicialNatural (Horn missing) (Boundary n)
hornToBoundary {n} missing = selectedInclusion
  {S = exceptFace missing} {T = allFaces n} (λ j p → tt)

hornToBoundary-inclusion : {n : ℕ} (missing : Facet n)
  → hornToBoundary missing ⋆s boundaryInclusion n ≡ hornInclusion missing
hornToBoundary-inclusion missing = simplicialNaturalExt λ m c → refl
