{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.SelectedGraphPresentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.FiniteFaceIndices
open import DHH.StableNerve.Nerve
import DHH.Cubical.SelectedFinitePresentation as SP
import DHH.Cubical.GraphPresentation as GP

-- 按有限面呈示构造的实际图：顶点由各张网格的顶点粘合；边也从
-- 同一张网格的边生成。不能把它替换成“立方体中这些顶点的诱导
-- 子图”：二维三边 horn 的四个顶点会诱导出第四条不该有的边。
module SelectedGraph (m : ℕ) {n : ℕ} (S : FaceSelection n)
  (Nodes : Enumeration (SelectedFacet S))
  (Overlaps : Enumeration (SelectedCodim2 S)) where
  module M = SP.SelectedPresentation S Nodes Overlaps
  module F = SelectedFaces S
  module V = GP.GraphPresentation m (count Nodes) M.nodeDimension (count Overlaps) M.relations

  graph : Graph ℓ-zero
  graph = V.graph

  -- 比较是在所有维数上自然的。给定一个 horn 图上的图映射，程序
  -- 先解释有限的节点与关系，再经已验证的呈示逆映射生成整个 horn。
  toSelected : {ℓ : Level} (G : Graph ℓ) → Hom graph G
    → CubicalNatural F.complex (Nₘ m G)
  toSelected G f = M.presentationComparisonInverse ⋆n V.toNerveMap G f

  fromSelected : {ℓ : Level} (G : Graph ℓ)
    → CubicalNatural F.complex (Nₘ m G) → Hom graph G
  fromSelected G f = V.fromNerveMap G (M.presentationComparison ⋆n f)

  to-from : {ℓ : Level} (G : Graph ℓ) (f : CubicalNatural F.complex (Nₘ m G))
    → toSelected G (fromSelected G f) ≡ f
  to-from G f = cubicalNaturalExt
    {A = F.complex} {B = Nₘ m G}
    {f = toSelected G (fromSelected G f)} {g = f}
    (λ k c → cong (λ h → mapCells h k (mapCells M.presentationComparisonInverse k c))
        (V.to-from G (M.presentationComparison ⋆n f))
      ∙ cong (mapCells f k)
        (cong (λ h → mapCells h k c) M.presentationComparison-right))

  from-to : {ℓ : Level} (G : Graph ℓ) (f : Hom graph G)
    → fromSelected G (toSelected G f) ≡ f
  from-to G f = cong (V.fromNerveMap G) (cubicalNaturalExt
      {A = M.P.complex} {B = Nₘ m G}
      {f = M.presentationComparison ⋆n toSelected G f} {g = V.toNerveMap G f}
      (λ k c → cong (mapCells (V.toNerveMap G f) k)
        (cong (λ h → mapCells h k c) M.presentationComparison-left)))
    ∙ V.from-to G f

  selectedGraphNerveIso : {ℓ : Level} (G : Graph ℓ)
    → Iso (Hom graph G) (CubicalNatural F.complex (Nₘ m G))
  Iso.fun (selectedGraphNerveIso G) = toSelected G
  Iso.inv (selectedGraphNerveIso G) = fromSelected G
  Iso.rightInv (selectedGraphNerveIso G) = to-from G
  Iso.leftInv (selectedGraphNerveIso G) = from-to G

module BoundaryGraph (m n : ℕ) where
  module Parameters = SP.BoundaryPresentation n
  module Model = SelectedGraph m (allFaces n) Parameters.Nodes Parameters.Overlaps
  open Model public

module OpenBoxGraph (m : ℕ) {n : ℕ} (missing : Facet n) where
  module Parameters = SP.OpenBoxPresentation missing
  module Model = SelectedGraph m (exceptFace missing) Parameters.Nodes Parameters.Overlaps
  open Model public

-- 泛性质描述图如何记住粘接数据，不是枚举目标图的所有映射。
-- 尚未在这里构造扩网格 retraction，或声称某个 unit 是弱等价。
