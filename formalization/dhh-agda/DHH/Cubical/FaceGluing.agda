{-# OPTIONS --cubical --safe #-}

module DHH.Cubical.FaceGluing where

-- 研究视角：将“给每个点指定值”改写成“在生成的面上给数据，再证相容”。
-- 下面的粘合与唯一性是已证结果；下一项候选工作是把所有重索引下的
-- agreeOnOverlap 归约为有限生成的相交规律。若成功，输入边界的编码会
-- 更紧凑；但有限相容性准则在本模块尚未证明，更不直接产生内部填充。

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Faces

private variable ℓ : Level

-- 把“在若干面上给出数据”变为整个子预层上的映射。
-- agreeOnOverlap 明确要求不同分解代表给出相同结果；有了这份证明，
-- 命题截断可以弱常值地消去到 cell 集合，不必挑选规范代表元。
-- 这里的 agreeOnOverlap 检查所有重索引的相交，不声称已化成有限个邻面等式。
module Gluing {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ) where
  module F = SelectedFaces S

  record FaceData : Type ℓ where
    field
      faceCell : (j : Facet n) → fst (S j) → Cell A n
      agreeOnOverlap : (j k : Facet n) (p : fst (S j)) (q : fst (S k))
        {m : ℕ} (u v : CubicalMap m n)
        → u ⋆c facetMap j ≡ v ⋆c facetMap k
        → reindex A u (faceCell j p) ≡ reindex A v (faceCell k q)
  open FaceData public

  module _ (D : FaceData) where
    evaluateFactor : {m : ℕ} (u : CubicalMap m (suc n)) → F.Factorization u → Cell A m
    evaluateFactor u (j , p , v , e) = reindex A v (faceCell D j p)

    factor-independent : {m : ℕ} (u : CubicalMap m (suc n))
      (r s : F.Factorization u) → evaluateFactor u r ≡ evaluateFactor u s
    factor-independent u (j , p , v , e) (k , q , w , d) =
      agreeOnOverlap D j k p q v w (e ∙ sym d)

    value : {m : ℕ} (u : CubicalMap m (suc n)) → F.Contains u → Cell A m
    value {m} u = PT.rec→Set (snd (cells A m)) (evaluateFactor u) (factor-independent u)

    -- 构造跟随“分解—解释—组合”的模式：在一个代表上执行 reindex，
    -- 然后用 agreeOnOverlap 证明其不依赖代表。自然性由 reindex-compose 统一给出。
    assemble : CubicalNatural F.complex A
    mapCells assemble m (u , p) = value u p
    natural assemble {m} {k} f (u , p) = PT.elim
      {P = λ q → value (f ⋆c u) (F.restrict f u q) ≡ reindex A f (value u q)}
      (λ q → snd (cells A m) _ _)
      (λ { (j , selected , v , e) → reindex-compose A f v (faceCell D j selected) }) p

    assemble-on-face : (j : Facet n) (p : fst (S j))
      → F.face j p ⋆n assemble ≡ classifyCube A (faceCell D j p)
    assemble-on-face j p = cubicalNaturalExt λ m u → refl

    -- 唯一性把证明负担缩回生成面：两个全局映射在各生成面上一致即可。
    -- 这不提供缺失面的填充，却给后续递归构造填充时可复用的粘接接口。
    assemble-unique : (h : CubicalNatural F.complex A)
      → ((j : Facet n) (p : fst (S j))
          → F.face j p ⋆n h ≡ classifyCube A (faceCell D j p))
      → h ≡ assemble
    assemble-unique h eq = cubicalNaturalExt λ m (u , p) → PT.elim
      {P = λ q → mapCells h m (u , q) ≡ value u q}
      (λ q → snd (cells A m) _ _)
      (λ { (j , selected , v , e) →
        sym (cong (mapCells h m) (Σ≡Prop (λ _ → squash₁)
          {u = (v ⋆c facetMap j) , ∣ j , selected , v , refl ∣₁}
          {v = u , ∣ j , selected , v , e ∣₁} e))
        ∙ cong (λ f → mapCells f m v) (eq j selected) }) p
