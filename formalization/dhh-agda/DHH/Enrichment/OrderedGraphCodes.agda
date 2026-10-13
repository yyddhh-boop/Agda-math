{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.OrderedGraphCodes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Ordinal.Base using (Ord; isSetOrd)
open import Cubical.Relation.Binary.Order.Woset.Base using (WosetStr)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Graph
open import DHH.GraphSets

private variable ℓ ℓ' : Level

-- Ord 的对象路径必须保留良序结构；库用良基性与弱外延性证明
-- isSetOrd。任意图的顶点置换无需保留良序，所以 Graph 的非平凡
-- 同构回路不会在这里变成对象路径。这是严格对象编码的一条受限路线。
-- 库中的良序结构准确包含命题值、良基、弱外延、传递，不额外
-- 假设经典三歧律。编码不限制载体为有限集，也不要求可计算枚举。
OrderedAdjacency : (α : Ord {ℓ}) → Type (ℓ-suc ℓ)
OrderedAdjacency {ℓ} α = ⟨ α ⟩ → ⟨ α ⟩ → hProp ℓ

OrderedGraphLaws : (α : Ord {ℓ}) → OrderedAdjacency α → Type ℓ
OrderedGraphLaws α E =
  ((x : ⟨ α ⟩) → fst (E x x)) ×
  ((x y : ⟨ α ⟩) → fst (E x y) → fst (E y x))

orderedGraphLaws-isProp : (α : Ord {ℓ}) (E : OrderedAdjacency α)
  → isProp (OrderedGraphLaws α E)
orderedGraphLaws-isProp α E =
  isProp× (isPropΠ (λ x → snd (E x x)))
    (isPropΠ3 (λ x y _ → snd (E y x)))

OrderedGraphCode : (ℓ : Level) → Type (ℓ-suc ℓ)
OrderedGraphCode ℓ = Σ[ α ∈ Ord {ℓ} ]
  Σ[ E ∈ OrderedAdjacency α ] OrderedGraphLaws α E

orderedGraphCode-isSet : isSet (OrderedGraphCode ℓ)
orderedGraphCode-isSet = isSetΣ isSetOrd λ α →
  isSetΣSndProp (isSetΠ2 (λ _ _ → isSetHProp))
    (orderedGraphLaws-isProp α)

decodeOrderedGraph : OrderedGraphCode ℓ → Graph ℓ
Vertex (decodeOrderedGraph (α , E , laws)) = ⟨ α ⟩
vertex-isSet (decodeOrderedGraph (α , E , laws)) = WosetStr.is-set (snd α)
Adj (decodeOrderedGraph (α , E , laws)) x y = fst (E x y)
adj-isProp (decodeOrderedGraph (α , E , laws)) x y = snd (E x y)
adj-refl (decodeOrderedGraph (α , E , laws)) = fst laws
adj-sym (decodeOrderedGraph (α , E , laws)) {x} {y} = snd laws x y

-- 这是输入已给定良序后的构造，不是从 isSet Vertex 选出一个良序。
-- 仅仅 ∥ WosetStr ℓ (Vertex G) ∥₁ 也不会被消去成一个选定编码。
encodeOrderedGraph : (G : Graph ℓ) → WosetStr ℓ (Vertex G)
  → OrderedGraphCode ℓ
encodeOrderedGraph G order = (Vertex G , order) ,
  (λ x y → Adj G x y , adj-isProp G x y) ,
  (adj-refl G , λ x y → adj-sym G)

orderedGraphDecodeEncode : (G : Graph ℓ) (order : WosetStr ℓ (Vertex G))
  → decodeOrderedGraph (encodeOrderedGraph G order) ≡ G
Vertex (orderedGraphDecodeEncode G order i) = Vertex G
vertex-isSet (orderedGraphDecodeEncode G order i) =
  isPropIsSet (WosetStr.is-set order) (vertex-isSet G) i
Adj (orderedGraphDecodeEncode G order i) = Adj G
adj-isProp (orderedGraphDecodeEncode G order i) = adj-isProp G
adj-refl (orderedGraphDecodeEncode G order i) = adj-refl G
adj-sym (orderedGraphDecodeEncode G order i) = adj-sym G

record GraphIso (G : Graph ℓ) (H : Graph ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    forward : Hom G H
    backward : Hom H G
    section : forward ∘g backward ≡ idHom H
    retraction : backward ∘g forward ≡ idHom G
open GraphIso public

-- 覆盖定理有显式量词：每个附带所需良序的图，解码后与原图同构。
-- 正反映射使用原顶点与原邻接，既没有取商，也没有舍弃无限图。
orderedGraphRepresentation : (G : Graph ℓ) (order : WosetStr ℓ (Vertex G))
  → GraphIso (decodeOrderedGraph (encodeOrderedGraph G order)) G
onVertices (forward (orderedGraphRepresentation G order)) x = x
preserves (forward (orderedGraphRepresentation G order)) e = e
onVertices (backward (orderedGraphRepresentation G order)) x = x
preserves (backward (orderedGraphRepresentation G order)) e = e
section (orderedGraphRepresentation G order) = homExt (λ _ → refl)
retraction (orderedGraphRepresentation G order) = homExt (λ _ → refl)

-- 对象编码带良序，但态射仍是所有原图同态，不要求态射保序。
-- 因此选择良序只刚化对象表示，没有改变所表示两图之间的 Hom。
OrderedGraphCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (OrderedGraphCategory ℓ) = OrderedGraphCode ℓ
Category.Hom[_,_] (OrderedGraphCategory ℓ) c d =
  Hom (decodeOrderedGraph c) (decodeOrderedGraph d)
Category.id (OrderedGraphCategory ℓ) {x = c} = idHom (decodeOrderedGraph c)
Category._⋆_ (OrderedGraphCategory ℓ) f g = g ∘g f
Category.⋆IdL (OrderedGraphCategory ℓ) = rightIdentity
Category.⋆IdR (OrderedGraphCategory ℓ) = leftIdentity
Category.⋆Assoc (OrderedGraphCategory ℓ) f g h = sym (associativity h g f)
Category.isSetHom (OrderedGraphCategory ℓ) = isSetGraphHom

decodeOrderedGraphFunctor : (ℓ : Level)
  → Functor (OrderedGraphCategory ℓ) (GraphCategory ℓ)
Functor.F-ob (decodeOrderedGraphFunctor ℓ) = decodeOrderedGraph
Functor.F-hom (decodeOrderedGraphFunctor ℓ) f = f
Functor.F-id (decodeOrderedGraphFunctor ℓ) = refl
Functor.F-seq (decodeOrderedGraphFunctor ℓ) f g = refl

-- orderedGraphCode-isSet 可以用于经典 nerve 的对象集合字段。
-- 这还没有提供整个 GraphCategory 的严格对象集合：若要恢复原论文
-- 对全部图的陈述，仍需明确的额外基础或全对象编码比较，不能省去。
