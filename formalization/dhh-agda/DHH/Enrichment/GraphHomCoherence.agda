{-# OPTIONS --cubical --safe #-}

module DHH.Enrichment.GraphHomCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (PointGraph)
open import DHH.Enrichment.GraphHom

private variable ℓA ℓB ℓC ℓD : Level

-- 所有图的宇宙分别泛化；只消去 BOX 边的两个结构分支。
boxMap : {A : Graph ℓA} {B : Graph ℓB} {C : Graph ℓC} {D : Graph ℓD}
  → Hom A B → Hom C D → Hom (A BOX C) (B BOX D)
onVertices (boxMap f g) (a , c) = onVertices f a , onVertices g c
preserves (boxMap {B = B} {D = D} f g) = PT.rec (adj-isProp (B BOX D) _ _) λ where
  (inl (e , a)) → ∣ inl (cong (onVertices f) e , preserves g a) ∣₁
  (inr (a , e)) → ∣ inr (preserves f a , cong (onVertices g) e) ∣₁

boxAssociate : (A : Graph ℓA) (B : Graph ℓB) (C : Graph ℓC)
  → Hom ((A BOX B) BOX C) (A BOX (B BOX C))
onVertices (boxAssociate A B C) ((a , b) , c) = a , (b , c)
preserves (boxAssociate A B C) = PT.rec (adj-isProp (A BOX (B BOX C)) _ _) λ where
  (inl (e , c)) → ∣ inl (cong fst e , ∣ inl (cong snd e , c) ∣₁) ∣₁
  (inr (ab , e)) → PT.rec (adj-isProp (A BOX (B BOX C)) _ _)
    (λ where
      (inl (a , b)) → ∣ inl (a , ∣ inr (b , e) ∣₁) ∣₁
      (inr (a , b)) → ∣ inr (a , (λ i → b i , e i)) ∣₁) ab

boxLeftUnit : (A : Graph ℓA) → Hom (PointGraph BOX A) A
onVertices (boxLeftUnit A) (_ , a) = a
preserves (boxLeftUnit A) {x = (_ , a)} {y = (_ , b)} = PT.rec (adj-isProp A a b) λ where
  (inl (_ , e)) → e
  (inr (_ , e)) → subst (Adj A a) e (adj-refl A a)

boxRightUnit : (A : Graph ℓA) → Hom (A BOX PointGraph) A
onVertices (boxRightUnit A) (a , _) = a
preserves (boxRightUnit A) {x = (a , _)} {y = (b , _)} = PT.rec (adj-isProp A a b) λ where
  (inl (e , _)) → subst (Adj A a) e (adj-refl A a)
  (inr (e , _)) → e

identityGraph : (G : Graph ℓA) → Hom PointGraph (HomGraph G G)
identityGraph G = constantHom (HomGraph G G) (identityVertex G)

-- 把点上的单位/结合等式提升为图态射相等，两个图示路线的
-- 定义域已用真实 BOX 结合子/单位子对齐，没有仅比较类型不同的式子。
composition-graph-left-unit : (G : Graph ℓA) (H : Graph ℓB)
  → compositionGraph {G = G} {H = H} {K = H}
      ∘g boxMap (identityGraph H) (idHom (HomGraph G H))
    ≡ boxLeftUnit (HomGraph G H)
composition-graph-left-unit G H = homExt (λ _ → homExt (λ _ → refl))

composition-graph-right-unit : (G : Graph ℓA) (H : Graph ℓB)
  → compositionGraph {G = G} {H = G} {K = H}
      ∘g boxMap (idHom (HomGraph G H)) (identityGraph G)
    ≡ boxRightUnit (HomGraph G H)
composition-graph-right-unit G H = homExt (λ _ → homExt (λ _ → refl))

composition-graph-associativity : (G : Graph ℓA) (H : Graph ℓB) (K : Graph ℓC) (L : Graph ℓD)
  → compositionGraph {G = G} {H = H} {K = L}
      ∘g boxMap (compositionGraph {G = H} {H = K} {K = L}) (idHom (HomGraph G H))
    ≡ compositionGraph {G = G} {H = K} {K = L}
      ∘g boxMap (idHom (HomGraph K L)) (compositionGraph {G = G} {H = H} {K = K})
      ∘g boxAssociate (HomGraph K L) (HomGraph H K) (HomGraph G H)
composition-graph-associativity G H K L = homExt (λ _ → homExt (λ _ → refl))

-- 这里只证明图富集复合的三个相干图；尚未构造立方体 Day tensor，
-- 也未由此断言 N∞ 保持该 tensor 或原始 DHH 已经成立。
