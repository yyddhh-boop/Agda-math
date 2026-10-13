{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.SelectedFinitePresentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.FaceIntersections
open import DHH.Cubical.FiniteFaceIndices
import DHH.Cubical.FinitePresentation as FP

-- 输入是实际的完整有限枚举，不假设一份呈示与选面预层同构。
-- 每个选中面给一个维数 n 的节点，每个选中的余维二交集给一条
-- 关系；FaceIntersections 证明这份有限关系已经控制所有重索引交集。
module SelectedPresentation {n : ℕ} (S : FaceSelection n)
  (Nodes : Enumeration (SelectedFacet S))
  (Overlaps : Enumeration (SelectedCodim2 S)) where
  module F = SelectedFaces S

  nodeDimension : Fin (count Nodes) → ℕ
  nodeDimension i = n

  selectedLeft selectedRight : SelectedCodim2 S → SelectedFacet S
  selectedLeft z = lowerFacet (fst z) , fst (snd z)
  selectedRight z = upperFacet (fst z) , snd (snd z)

  relationFor : SelectedCodim2 S → FP.Relation nodeDimension
  FP.relationDimension (relationFor z) = intersectionDimension n
  FP.leftNode (relationFor z) = number Nodes (selectedLeft z)
  FP.rightNode (relationFor z) = number Nodes (selectedRight z)
  FP.leftMap (relationFor z) = lowerOverlap (fst z)
  FP.rightMap (relationFor z) = upperOverlap (fst z)

  relations : Fin (count Overlaps) → FP.Relation nodeDimension
  relations i = relationFor (enumerate Overlaps i)

  module P = FP.Presentation (count Nodes) nodeDimension (count Overlaps) relations

  -- 在选面复形中的生成 cell 底层正是 facetMap。包含证明用 identity
  -- 的一步分解构造，不依赖规范词或任意的代表选择。
  facetCell : SelectedFacet S → Cell F.complex n
  facetCell (j , p) = facetMap j , ∣ j , p , cubeId n , Category.⋆IdL CubeCategory (facetMap j) ∣₁

  nodeCells : (i : Fin (count Nodes)) → Cell F.complex (nodeDimension i)
  nodeCells i = facetCell (enumerate Nodes i)

  selectedRelations : (z : SelectedCodim2 S)
    → P.Equation F.complex nodeCells (relationFor z)
  selectedRelations z =
    cong (reindex F.complex (lowerOverlap (fst z)))
      (cong facetCell (enumerate-number Nodes (selectedLeft z)))
    ∙ Σ≡Prop (λ _ → squash₁) (overlap-square (fst z))
    ∙ sym (cong (reindex F.complex (upperOverlap (fst z)))
      (cong facetCell (enumerate-number Nodes (selectedRight z))))

  module ToSelected = P.Interpret F.complex nodeCells
    (λ i → selectedRelations (enumerate Overlaps i))

  presentationComparison : CubicalNatural P.complex F.complex
  presentationComparison = ToSelected.factor

  -- 有限关系列表的 node-relations 经枚举的右逆还原为所有实际交集。
  -- 这里使用的是已构造的 quotient 关系，并没有再假定 overlap 相容。
  presentationFaceCells : (j : Facet n) → fst (S j) → Cell P.complex n
  presentationFaceCells j p = P.nodeCell (number Nodes (j , p))

  allPresentationRelations : (z : SelectedCodim2 S)
    → P.Equation P.complex P.nodeCell (relationFor z)
  allPresentationRelations z = subst
    (λ t → P.Equation P.complex P.nodeCell (relationFor t))
    (enumerate-number Overlaps z) (P.node-relations (number Overlaps z))

  presentationRawAgreement : RawAgreement S P.complex presentationFaceCells
  presentationRawAgreement = allPresentationRelations

  presentationFaceData : PairwiseFaceData S P.complex
  presentationFaceData = fromRawAgreement S P.complex presentationFaceCells presentationRawAgreement

  module FromSelected = FiniteGluing S P.complex presentationFaceData

  presentationComparisonInverse : CubicalNatural F.complex P.complex
  presentationComparisonInverse = FromSelected.assemble

  facetCell-as-face : (j : SelectedFacet S)
    → facetCell j ≡ mapCells (F.face (fst j) (snd j)) n (cubeId n)
  facetCell-as-face j = Σ≡Prop (λ _ → squash₁)
    (sym (Category.⋆IdL CubeCategory (facetMap (fst j))))

  inverse-on-facet : (j : SelectedFacet S)
    → mapCells presentationComparisonInverse n (facetCell j) ≡ P.nodeCell (number Nodes j)
  inverse-on-facet j =
    cong (mapCells presentationComparisonInverse n) (facetCell-as-face j)
    ∙ cong (λ f → mapCells f n (cubeId n)) (FromSelected.assemble-on-face (fst j) (snd j))
    ∙ reindex-id P.complex (P.nodeCell (number Nodes j))

  inverse-on-node : (i : Fin (count Nodes))
    → mapCells presentationComparisonInverse n (nodeCells i) ≡ P.nodeCell i
  inverse-on-node i = inverse-on-facet (enumerate Nodes i)
    ∙ cong P.nodeCell (number-enumerate Nodes i)

  -- 第一逆式沿商的生成元归纳；自然性把任意来源维数的 map 缩回
  -- 有限 node，再使用上面的 inverse-on-node。
  presentationComparison-left
    : presentationComparison ⋆n presentationComparisonInverse ≡ cubicalId P.complex
  presentationComparison-left = cubicalNaturalExt
    {A = P.complex} {B = P.complex}
    {f = presentationComparison ⋆n presentationComparisonInverse}
    {g = cubicalId P.complex}
    (λ m → SQ.elimProp (λ c → SQ.squash/ _ _)
      (λ { (i , u) → natural presentationComparisonInverse u (nodeCells i)
        ∙ cong (reindex P.complex u) (inverse-on-node i)
        ∙ P.node-reindex i u }))

  selected-on-facet : (j : SelectedFacet S)
    → mapCells (presentationComparisonInverse ⋆n presentationComparison) n (facetCell j)
      ≡ facetCell j
  selected-on-facet j =
    cong (mapCells presentationComparison n) (inverse-on-facet j)
    ∙ ToSelected.factor-on-node (number Nodes j)
    ∙ cong facetCell (enumerate-number Nodes j)

  -- 第二逆式消去“经过选中面分解”的截断。输出是 cell 集合中的
  -- 等式，故合法用命题消去；没有从 Contains 选择某个规范分解。
  presentationComparison-right
    : presentationComparisonInverse ⋆n presentationComparison ≡ cubicalId F.complex
  presentationComparison-right = cubicalNaturalExt
    {A = F.complex} {B = F.complex}
    {f = presentationComparisonInverse ⋆n presentationComparison}
    {g = cubicalId F.complex}
    (λ m c → PT.elim
      {P = λ p → mapCells (presentationComparisonInverse ⋆n presentationComparison) m (fst c , p)
        ≡ (fst c , p)}
      (λ p → snd (cells F.complex m) _ _)
      (λ { (j , selected , v , e) →
        let t = j , selected
            change : (fst c , ∣ j , selected , v , e ∣₁) ≡ reindex F.complex v (facetCell t)
            change = Σ≡Prop (λ _ → squash₁) (sym e)
        in cong (mapCells (presentationComparisonInverse ⋆n presentationComparison) m) change
          ∙ natural (presentationComparisonInverse ⋆n presentationComparison) v (facetCell t)
          ∙ cong (reindex F.complex v) (selected-on-facet t)
          ∙ sym change })
      (snd c))

-- Boundary 与 OpenBox 的选择是可判定的，故所需两份有限枚举完全
-- 由过滤算法计算。任意未给决定性的 hProp 选面不会被偷偷枚举。
module DecidablePresentation {n : ℕ} (S : FaceSelection n) (dec : DecSelection S) where
  Nodes : Enumeration (SelectedFacet S)
  Nodes = selectedFacetEnumeration S dec
  Overlaps : Enumeration (SelectedCodim2 S)
  Overlaps = selectedCodim2Enumeration S dec
  module Constructed = SelectedPresentation S Nodes Overlaps
  open Constructed public

module BoundaryPresentation (n : ℕ) where
  module Model = DecidablePresentation (allFaces n) (boundaryDecision n)
  open Model public

module OpenBoxPresentation {n : ℕ} (missing : Facet n) where
  module Model = DecidablePresentation (exceptFace missing) (openBoxDecision missing)
  open Model public
