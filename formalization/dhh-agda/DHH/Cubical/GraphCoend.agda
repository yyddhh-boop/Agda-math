{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.GraphCoend where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve

private variable ℓ ℓ' ℓ'' : Level

-- Γ_m 以所有 cell 为网格生成块。来源预层和目地图均可无限；
-- 输入 A 的 universe 保留为 ℓ，未把全部 cell 偷偷缩至 Type₀。
module GraphCoend {ℓ : Level} (m : ℕ) (A : CubicalSet ℓ) where
  VertexGenerator : Type ℓ
  VertexGenerator = Σ[ n ∈ ℕ ] Σ[ c ∈ Cell A n ] Vertex (Grid m n)

  data VertexIdentification : VertexGenerator → VertexGenerator → Type ℓ where
    glue : {i j : ℕ} (u : CubicalMap i j) (c : Cell A j) (x : Vertex (Grid m i))
      → VertexIdentification (i , reindex A u c , x)
        (j , c , onVertices (gridAction m u) x)

  Vertices : Type ℓ
  Vertices = VertexGenerator SQ./ VertexIdentification

  point : (n : ℕ) → Cell A n → Vertex (Grid m n) → Vertices
  point n c x = SQ.[ n , c , x ]

  identify : {i j : ℕ} (u : CubicalMap i j) (c : Cell A j) (x : Vertex (Grid m i))
    → point i (reindex A u c) x ≡ point j c (onVertices (gridAction m u) x)
  identify u c x = SQ.eq/ _ _ (glue u c x)

  -- 商顶点后的边仍须有一张共同网格作为见证。这保留缺面图的
  -- 正确边集，不会把全体商顶点改成环境图中的诱导子图。
  Edge : Vertices → Vertices → Type ℓ
  Edge x y = ∥ Σ[ n ∈ ℕ ] Σ[ c ∈ Cell A n ]
    Σ[ u ∈ Vertex (Grid m n) ] Σ[ v ∈ Vertex (Grid m n) ]
      (Adj (Grid m n) u v × (point n c u ≡ x) × (point n c v ≡ y)) ∥₁

  graph : Graph ℓ
  Vertex graph = Vertices
  vertex-isSet graph = SQ.squash/
  Adj graph = Edge
  adj-isProp graph _ _ = squash₁
  adj-refl graph = SQ.elimProp (λ _ → squash₁)
    (λ { (n , c , x) → ∣ n , c , x , x , adj-refl (Grid m n) x , refl , refl ∣₁ })
  adj-sym graph = PT.map (λ { (n , c , u , v , e , p , q) →
    n , c , v , u , adj-sym (Grid m n) e , q , p })

  includeGrid : (n : ℕ) → Cell A n → Hom (Grid m n) graph
  onVertices (includeGrid n c) = point n c
  preserves (includeGrid n c) {x} {y} e = ∣ n , c , x , y , e , refl , refl ∣₁

  include-natural : {i j : ℕ} (u : CubicalMap i j) (c : Cell A j)
    → includeGrid i (reindex A u c) ≡ includeGrid j c ∘g gridAction m u
  include-natural u c = homExt (identify u c)

  unit : CubicalNatural A (Nₘ m graph)
  mapCells unit = includeGrid
  natural unit = include-natural

  module Interpret (G : Graph ℓ') (η : CubicalNatural A (Nₘ m G)) where
    value : VertexGenerator → Vertex G
    value (n , c , x) = onVertices (mapCells η n c) x

    respects : (x y : VertexGenerator) → VertexIdentification x y → value x ≡ value y
    respects _ _ (glue u c x) = cong (λ f → onVertices f x) (natural η u c)

    vertexValue : Vertices → Vertex G
    vertexValue = SQ.rec (vertex-isSet G) value respects

    -- 先解释每个网格，再用 η 的全部自然性降商。保边只消去共同
    -- 网格的截断见证并运输其端点；没有使用图边的传递闭包。
    factor : Hom graph G
    onVertices factor = vertexValue
    preserves factor = PT.rec (adj-isProp G _ _)
      (λ { (n , c , u , v , edge , p , q) →
        subst2 (Adj G) (cong vertexValue p) (cong vertexValue q)
          (preserves (mapCells η n c) edge) })

    factor-on-grid : (n : ℕ) (c : Cell A n) → factor ∘g includeGrid n c ≡ mapCells η n c
    factor-on-grid n c = homExt (λ _ → refl)

    factor-unique : (h : Hom graph G)
      → ((n : ℕ) (c : Cell A n) → h ∘g includeGrid n c ≡ mapCells η n c)
      → h ≡ factor
    factor-unique h eqs = homExt (SQ.elimProp (λ _ → vertex-isSet G _ _)
      (λ { (n , c , x) → cong (λ f → onVertices f x) (eqs n c) }))

  toNerveMap : (G : Graph ℓ') → Hom graph G → CubicalNatural A (Nₘ m G)
  mapCells (toNerveMap G h) n c = h ∘g includeGrid n c
  natural (toNerveMap G h) u c = homExt (λ x → cong (onVertices h) (identify u c x))

  fromNerveMap : (G : Graph ℓ') → CubicalNatural A (Nₘ m G) → Hom graph G
  fromNerveMap G η = Interpret.factor G η

  -- 自然变换由各维的 cell 映射决定，图同态由商顶点决定。两逆
  -- 分别沿这些消去原则证明，不需要为任何商元素选代表。
  to-from : (G : Graph ℓ') (η : CubicalNatural A (Nₘ m G))
    → toNerveMap G (fromNerveMap G η) ≡ η
  to-from G η = cubicalNaturalExt
    {A = A} {B = Nₘ m G} {f = toNerveMap G (fromNerveMap G η)} {g = η}
    (λ n c → Interpret.factor-on-grid G η n c)

  from-to : (G : Graph ℓ') (h : Hom graph G) → fromNerveMap G (toNerveMap G h) ≡ h
  from-to G h = homExt (SQ.elimProp (λ _ → vertex-isSet G _ _)
    (λ { (n , c , x) → refl }))

  graphNerveIso : (G : Graph ℓ') → Iso (Hom graph G) (CubicalNatural A (Nₘ m G))
  Iso.fun (graphNerveIso G) = toNerveMap G
  Iso.inv (graphNerveIso G) = fromNerveMap G
  Iso.rightInv (graphNerveIso G) = to-from G
  Iso.leftInv (graphNerveIso G) = from-to G

  graphNerveEquivalence : (G : Graph ℓ') → Hom graph G ≃ CubicalNatural A (Nₘ m G)
  graphNerveEquivalence G = isoToEquiv (graphNerveIso G)

Γₘ : (m : ℕ) → CubicalSet ℓ → Graph ℓ
Γₘ m A = GraphCoend.graph m A

Γₘ-map : (m : ℕ) {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
  → CubicalNatural A B → Hom (Γₘ m A) (Γₘ m B)
Γₘ-map m {A = A} {B = B} η = GraphCoend.fromNerveMap m A (Γₘ m B)
  (η ⋆n GraphCoend.unit m B)

Γₘ-map-on-grid : (m : ℕ) {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
  (η : CubicalNatural A B) (n : ℕ) (c : Cell A n)
  → Γₘ-map m η ∘g GraphCoend.includeGrid m A n c
    ≡ GraphCoend.includeGrid m B n (mapCells η n c)
Γₘ-map-on-grid m η n c = homExt (λ _ → refl)

Γₘ-map-id : (m : ℕ) (A : CubicalSet ℓ) → Γₘ-map m (cubicalId A) ≡ idHom (Γₘ m A)
Γₘ-map-id m A = homExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ { (n , c , x) → refl }))

Γₘ-map-compose : (m : ℕ) {A : CubicalSet ℓ} {B : CubicalSet ℓ'} {C : CubicalSet ℓ''}
  (η : CubicalNatural A B) (θ : CubicalNatural B C)
  → Γₘ-map m (η ⋆n θ) ≡ Γₘ-map m θ ∘g Γₘ-map m η
Γₘ-map-compose m η θ = homExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ { (n , c , x) → refl }))

Γₘ-functor : (m : ℕ) (ℓ : Level) → Functor (CubicalSetCategory ℓ) (GraphCategory ℓ)
Functor.F-ob (Γₘ-functor m ℓ) = Γₘ m
Functor.F-hom (Γₘ-functor m ℓ) {x = A} {y = B} η = Γₘ-map m {A = A} {B = B} η
Functor.F-id (Γₘ-functor m ℓ) {x = A} = Γₘ-map-id m A
Functor.F-seq (Γₘ-functor m ℓ) {x = A} {y = B} {z = C} η θ =
  Γₘ-map-compose m {A = A} {B = B} {C = C} η θ

Nₘ-functor : (m : ℕ) (ℓ : Level) → Functor (GraphCategory ℓ) (CubicalSetCategory ℓ)
Functor.F-ob (Nₘ-functor m ℓ) = Nₘ m
Functor.F-hom (Nₘ-functor m ℓ) {x = G} {y = H} h = Nₘ-map m {G = G} {H = H} h
Functor.F-id (Nₘ-functor m ℓ) {x = G} = Nₘ-map-id m G
Functor.F-seq (Nₘ-functor m ℓ) {x = G} {y = H} {z = K} f g =
  Nₘ-map-compose m {G = G} {H = H} {K = K} f g

toNerve-postcompose : (m : ℕ) (A : CubicalSet ℓ) {G : Graph ℓ'} {H : Graph ℓ''}
  (h : Hom (Γₘ m A) G) (k : Hom G H)
  → GraphCoend.toNerveMap m A H (k ∘g h)
    ≡ GraphCoend.toNerveMap m A G h ⋆n Nₘ-map m k
toNerve-postcompose m A {G} {H} h k = cubicalNaturalExt
  {A = A} {B = Nₘ m H}
  {f = GraphCoend.toNerveMap m A H (k ∘g h)}
  {g = GraphCoend.toNerveMap m A G h ⋆n Nₘ-map m k}
  (λ n c → homExt (λ _ → refl))

fromNerve-precompose : (m : ℕ) {A : CubicalSet ℓ} {B : CubicalSet ℓ'} (G : Graph ℓ'')
  (η : CubicalNatural B (Nₘ m G)) (h : CubicalNatural A B)
  → GraphCoend.fromNerveMap m A G (h ⋆n η)
    ≡ GraphCoend.fromNerveMap m B G η ∘g Γₘ-map m h
fromNerve-precompose m G η h = homExt (SQ.elimProp (λ _ → vertex-isSet G _ _)
  (λ { (n , c , x) → refl }))

-- counit 是实际评价：(n,f,x) ↦ f(x)。这只给伴随，不声称 unit
-- 或 counit 是弱等价；原 DHH 的同伦比较仍须独立证明。
counit : (m : ℕ) (G : Graph ℓ) → Hom (Γₘ m (Nₘ m G)) G
counit m G = GraphCoend.fromNerveMap m (Nₘ m G) G (cubicalId (Nₘ m G))

triangle-graph : (m : ℕ) (A : CubicalSet ℓ)
  → counit m (Γₘ m A) ∘g Γₘ-map m (GraphCoend.unit m A) ≡ idHom (Γₘ m A)
triangle-graph m A = homExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ { (n , c , x) → refl }))

triangle-nerve : (m : ℕ) (G : Graph ℓ)
  → GraphCoend.unit m (Nₘ m G) ⋆n Nₘ-map m (counit m G) ≡ cubicalId (Nₘ m G)
triangle-nerve m G = cubicalNaturalExt
  {A = Nₘ m G} {B = Nₘ m G}
  {f = GraphCoend.unit m (Nₘ m G) ⋆n Nₘ-map m (counit m G)}
  {g = cubicalId (Nₘ m G)}
  (λ n c → homExt (λ _ → refl))
