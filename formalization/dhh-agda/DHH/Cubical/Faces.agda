{-# OPTIONS --cubical --safe #-}

module DHH.Cubical.Faces where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Cubes using (Position)
open import DHH.CubeCategory
open import DHH.CubicalNerve

-- 构造思路：一个 (n+1)-立方体有 2(n+1) 个面，编码为位置与端点。
-- 选取若干面后，其生成的子预层包含每个面的所有重索引。
-- 用“经过某个选中的面分解”的命题定义 cell，自动处理重复表达；
-- 无需按维度列举这个子预层中的所有退化 cell。
-- n 始终比被围住的立方体维数小 1；没有把零维立方体称作 open box。
Facet : ℕ → Type₀
Facet n = Position (suc n) × Bool

facetMap : {n : ℕ} → Facet n → CubicalMap n (suc n)
facetMap (i , b) = cubeFace i b

FaceSelection : ℕ → Type₁
FaceSelection n = Facet n → hProp ℓ-zero

module SelectedFaces {n : ℕ} (S : FaceSelection n) where
  Factorization : {m : ℕ} → CubicalMap m (suc n) → Type₀
  Factorization {m} u = Σ[ j ∈ Facet n ]
    (fst (S j) × (Σ[ v ∈ CubicalMap m n ] (v ⋆c facetMap j ≡ u)))

  Contains : {m : ℕ} → CubicalMap m (suc n) → Type₀
  Contains u = ∥ Factorization u ∥₁

  -- 对给定的分解代表做预合成。结合律把一步的构造推广到所有算子。
  restrict : {l m : ℕ} (f : CubicalMap l m) (u : CubicalMap m (suc n))
    → Contains u → Contains (f ⋆c u)
  restrict f u = PT.map λ { (j , selected , v , e) →
    j , selected , (f ⋆c v) ,
    (Category.⋆Assoc CubeCategory f v (facetMap j) ∙ cong (f ⋆c_) e) }

  complex : CubicalSet ℓ-zero
  cells complex m = (Σ[ u ∈ CubicalMap m (suc n) ] Contains u) ,
    isSetΣSndProp isSetCubicalMap (λ _ → squash₁)
  reindex complex f (u , p) = (f ⋆c u) , restrict f u p
  reindex-id complex (u , p) = Σ≡Prop (λ _ → squash₁) (Category.⋆IdL CubeCategory u)
  reindex-compose complex f g (u , p) = Σ≡Prop (λ _ → squash₁)
    (Category.⋆Assoc CubeCategory f g u)

  inclusion : CubicalNatural complex (RepresentableCube (suc n))
  mapCells inclusion m = fst
  natural inclusion f c = refl

  inclusion-injective : {m : ℕ} (x y : Cell complex m)
    → mapCells inclusion m x ≡ mapCells inclusion m y → x ≡ y
  inclusion-injective x y e = Σ≡Prop (λ _ → squash₁) e

  face : (j : Facet n) → fst (S j) → CubicalNatural (RepresentableCube n) complex
  mapCells (face j p) m v = (v ⋆c facetMap j) , ∣ j , p , v , refl ∣₁
  natural (face j p) f v = Σ≡Prop (λ _ → squash₁)
    (Category.⋆Assoc CubeCategory f v (facetMap j))

  face-inclusion : (j : Facet n) (p : fst (S j))
    → face j p ⋆n inclusion ≡ classifyCube (RepresentableCube (suc n)) (facetMap j)
  face-inclusion j p = cubicalNaturalExt λ m v → refl

allFaces : (n : ℕ) → FaceSelection n
allFaces n j = Unit , isPropUnit

exceptFace : {n : ℕ} → Facet n → FaceSelection n
exceptFace missing j = (¬ (j ≡ missing)) , isPropΠ (λ _ → Empty.isProp⊥)

Boundary : (n : ℕ) → CubicalSet ℓ-zero
Boundary n = SelectedFaces.complex (allFaces n)

OpenBox : {n : ℕ} → Facet n → CubicalSet ℓ-zero
OpenBox missing = SelectedFaces.complex (exceptFace missing)

boundaryInclusion : (n : ℕ) → CubicalNatural (Boundary n) (RepresentableCube (suc n))
boundaryInclusion n = SelectedFaces.inclusion (allFaces n)

openBoxInclusion : {n : ℕ} (missing : Facet n)
  → CubicalNatural (OpenBox missing) (RepresentableCube (suc n))
openBoxInclusion missing = SelectedFaces.inclusion (exceptFace missing)

-- 后续研究：有限个面生成整个边界，但其相容性必须被证明。
-- 这里没有选择分解的规范代表，也没有把“缺面”自动解释为存在填充。

-- 扩大选中的面集合只需传递选择证明；底层 cube morphism 保持不变。
-- 这把“删去一个面所得的是边界的子对象”写成实际自然映射。
selectedInclusion : {n : ℕ} {S T : FaceSelection n}
  → ((j : Facet n) → fst (S j) → fst (T j))
  → CubicalNatural (SelectedFaces.complex S) (SelectedFaces.complex T)
mapCells (selectedInclusion inc) m (u , p) = u ,
  PT.map (λ { (j , selected , v , e) → j , inc j selected , v , e }) p
natural (selectedInclusion inc) f (u , p) = Σ≡Prop (λ _ → squash₁) refl

openBoxToBoundary : {n : ℕ} (missing : Facet n)
  → CubicalNatural (OpenBox missing) (Boundary n)
openBoxToBoundary {n} missing = selectedInclusion
  {S = exceptFace missing} {T = allFaces n} (λ j p → tt)

openBoxToBoundary-inclusion : {n : ℕ} (missing : Facet n)
  → openBoxToBoundary missing ⋆n boundaryInclusion n ≡ openBoxInclusion missing
openBoxToBoundary-inclusion missing = cubicalNaturalExt λ m c → refl
