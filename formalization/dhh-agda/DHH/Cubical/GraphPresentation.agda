{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.GraphPresentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
import DHH.Cubical.FinitePresentation as FP

private variable ℓ : Level

module GraphPresentation (m r : ℕ) (dim : Fin r → ℕ)
                         (q : ℕ) (relations : Fin q → FP.Relation dim) where
  module P = FP.Presentation r dim q relations

  VertexGenerator : Type₀
  VertexGenerator = Σ[ i ∈ Fin r ] Vertex (Grid m (dim i))

  data VertexIdentification : VertexGenerator → VertexGenerator → Type₀ where
    identify : (e : Fin q) (x : Vertex (Grid m (FP.relationDimension (relations e))))
      → VertexIdentification
        (FP.leftNode (relations e) , onVertices (gridAction m (FP.leftMap (relations e))) x)
        (FP.rightNode (relations e) , onVertices (gridAction m (FP.rightMap (relations e))) x)

  Vertices : Type₀
  Vertices = VertexGenerator SQ./ VertexIdentification

  point : (i : Fin r) → Vertex (Grid m (dim i)) → Vertices
  point i x = SQ.[ i , x ]

  -- 关键：先商掉关系，再仅使用生成块里的边。若只取顶点并集的
  -- 诱导子图，三边horn的四个顶点会补回缺边；这里不会加这种边。
  Edge : Vertices → Vertices → Type₀
  Edge x y = ∥ Σ[ i ∈ Fin r ] Σ[ u ∈ Vertex (Grid m (dim i)) ]
    Σ[ v ∈ Vertex (Grid m (dim i)) ]
      (Adj (Grid m (dim i)) u v × (point i u ≡ x) × (point i v ≡ y)) ∥₁

  graph : Graph ℓ-zero
  Vertex graph = Vertices
  vertex-isSet graph = SQ.squash/
  Adj graph = Edge
  adj-isProp graph _ _ = squash₁
  adj-refl graph = SQ.elimProp (λ _ → squash₁)
    (λ { (i , x) → ∣ i , x , x , adj-refl (Grid m (dim i)) x , refl , refl ∣₁ })
  adj-sym graph = PT.map (λ { (i , u , v , e , p , t) →
    i , v , u , adj-sym (Grid m (dim i)) e , t , p })

  nodeGraph : (i : Fin r) → Hom (Grid m (dim i)) graph
  onVertices (nodeGraph i) = point i
  preserves (nodeGraph i) {x} {y} e = ∣ i , x , y , e , refl , refl ∣₁

  node-relations : (e : Fin q) → P.Equation (Nₘ m graph) nodeGraph (relations e)
  node-relations e = homExt (λ x → SQ.eq/ _ _ (identify e x))

  module Interpret (G : Graph ℓ) (xs : (i : Fin r) → Hom (Grid m (dim i)) G)
                   (eq : (e : Fin q) → P.Equation (Nₘ m G) xs (relations e)) where
    value : VertexGenerator → Vertex G
    value (i , x) = onVertices (xs i) x

    respects : (x y : VertexGenerator) → VertexIdentification x y → value x ≡ value y
    respects _ _ (identify e x) = cong (λ f → onVertices f x) (eq e)

    vertexValue : Vertices → Vertex G
    vertexValue = SQ.rec (vertex-isSet G) value respects

    -- 对生成顶点求值，关系正确性负责降商；保边证明从已选块的
    -- 原始边运输到商顶点。没有使用图边的传递性或额外填充边。
    factor : Hom graph G
    onVertices factor = vertexValue
    preserves factor = PT.rec (adj-isProp G _ _)
      (λ { (i , u , v , edge , p , t) →
        subst2 (Adj G) (cong vertexValue p) (cong vertexValue t)
          (preserves (xs i) edge) })

    factor-on-node : (i : Fin r) → factor ∘g nodeGraph i ≡ xs i
    factor-on-node i = homExt (λ _ → refl)

    factor-unique : (h : Hom graph G)
      → ((i : Fin r) → h ∘g nodeGraph i ≡ xs i) → h ≡ factor
    factor-unique h eqs = homExt (SQ.elimProp (λ _ → vertex-isSet G _ _)
      (λ { (i , x) → cong (λ f → onVertices f x) (eqs i) }))

  extractNodes : (G : Graph ℓ) → Hom graph G → (i : Fin r) → Hom (Grid m (dim i)) G
  extractNodes G h i = h ∘g nodeGraph i

  extractRelations : (G : Graph ℓ) (h : Hom graph G)
    → (e : Fin q) → P.Equation (Nₘ m G) (extractNodes G h) (relations e)
  extractRelations G h e = homExt (λ x →
    cong (onVertices h) (cong (λ f → onVertices f x) (node-relations e)))

  -- Γ_m 在这份有限呈示上的实际伴随：所有兼容网格映射既是图
  -- 粘接的同态，也恰好是整个呈示预层到N_m G的自然变换。
  toNerveMap : (G : Graph ℓ) → Hom graph G → CubicalNatural P.complex (Nₘ m G)
  toNerveMap G h = P.Interpret.factor (Nₘ m G) (extractNodes G h) (extractRelations G h)

  fromNerveMap : (G : Graph ℓ) → CubicalNatural P.complex (Nₘ m G) → Hom graph G
  fromNerveMap G h = Interpret.factor G
    (P.extractNodes (Nₘ m G) h) (P.extractRelations (Nₘ m G) h)

  to-from : (G : Graph ℓ) (h : CubicalNatural P.complex (Nₘ m G))
    → toNerveMap G (fromNerveMap G h) ≡ h
  to-from G h =
    P.Interpret.factor-unique (Nₘ m G) (P.extractNodes (Nₘ m G) h)
      (P.extractRelations (Nₘ m G) h) (toNerveMap G (fromNerveMap G h))
      (λ i → P.Interpret.factor-on-node (Nₘ m G)
        (extractNodes G (fromNerveMap G h)) (extractRelations G (fromNerveMap G h)) i
        ∙ Interpret.factor-on-node G (P.extractNodes (Nₘ m G) h)
          (P.extractRelations (Nₘ m G) h) i)
    ∙ sym (P.Interpret.factor-unique (Nₘ m G) (P.extractNodes (Nₘ m G) h)
        (P.extractRelations (Nₘ m G) h) h (λ _ → refl))

  from-to : (G : Graph ℓ) (h : Hom graph G) → fromNerveMap G (toNerveMap G h) ≡ h
  from-to G h =
    Interpret.factor-unique G (extractNodes G h) (extractRelations G h)
      (fromNerveMap G (toNerveMap G h))
      (λ i → Interpret.factor-on-node G (P.extractNodes (Nₘ m G) (toNerveMap G h))
        (P.extractRelations (Nₘ m G) (toNerveMap G h)) i
        ∙ P.Interpret.factor-on-node (Nₘ m G) (extractNodes G h) (extractRelations G h) i)
    ∙ sym (Interpret.factor-unique G (extractNodes G h) (extractRelations G h) h (λ _ → refl))

  graphNerveIso : (G : Graph ℓ) → Iso (Hom graph G) (CubicalNatural P.complex (Nₘ m G))
  Iso.fun (graphNerveIso G) = toNerveMap G
  Iso.inv (graphNerveIso G) = fromNerveMap G
  Iso.rightInv (graphNerveIso G) = to-from G
  Iso.leftInv (graphNerveIso G) = from-to G

  graphNerveEquivalence : (G : Graph ℓ) → Hom graph G ≃ CubicalNatural P.complex (Nₘ m G)
  graphNerveEquivalence G = isoToEquiv (graphNerveIso G)

  -- 这证明一个具体有限呈示的图实现泛性质，不宣称unit为弱等价。
  -- 图nerve可能新增mixed cubes；原DHH的全同伦比较仍须另外支付。
