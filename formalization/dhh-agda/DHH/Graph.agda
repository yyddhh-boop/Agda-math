{-# OPTIONS --cubical --safe #-}

module DHH.Graph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Ordinary (set-valued), reflexive, undirected graphs.  Adjacency carries
-- no proof multiplicity.  Vertices need not be finite.
record Graph (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Vertex : Type ℓ
    vertex-isSet : isSet Vertex
    Adj : Vertex → Vertex → Type ℓ
    adj-isProp : (x y : Vertex) → isProp (Adj x y)
    adj-refl : (x : Vertex) → Adj x x
    adj-sym : {x y : Vertex} → Adj x y → Adj y x

open Graph public

record Hom (G : Graph ℓ) (H : Graph ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    onVertices : Vertex G → Vertex H
    preserves : {x y : Vertex G} → Adj G x y
              → Adj H (onVertices x) (onVertices y)

open Hom public

idHom : (G : Graph ℓ) → Hom G G
onVertices (idHom G) x = x
preserves (idHom G) e = e

infixr 20 _∘g_
_∘g_ : {G : Graph ℓ} {H : Graph ℓ'} {K : Graph ℓ''}
     → Hom H K → Hom G H → Hom G K
onVertices (g ∘g f) x = onVertices g (onVertices f x)
preserves (g ∘g f) e = preserves g (preserves f e)

constantHom : {G : Graph ℓ} (H : Graph ℓ') → Vertex H → Hom G H
onVertices (constantHom H v) _ = v
preserves (constantHom H v) _ = adj-refl H v

-- BOX is Cartesian graph adjacency, not categorical graph adjacency:
-- only one coordinate changes.  Truncation identifies overlapping
-- witnesses, including the two ways to exhibit a loop.
BoxAdj : (G : Graph ℓ) (H : Graph ℓ')
       → (Vertex G × Vertex H) → (Vertex G × Vertex H)
       → Type (ℓ-max ℓ ℓ')
BoxAdj G H (x , u) (y , v) =
  ∥ ((x ≡ y) × Adj H u v) ⊎ (Adj G x y × (u ≡ v)) ∥₁

infixr 15 _BOX_
_BOX_ : Graph ℓ → Graph ℓ' → Graph (ℓ-max ℓ ℓ')
Vertex (G BOX H) = Vertex G × Vertex H
vertex-isSet (G BOX H) = isSet× (vertex-isSet G) (vertex-isSet H)
Adj (G BOX H) = BoxAdj G H
adj-isProp (G BOX H) _ _ = squash₁
adj-refl (G BOX H) (x , u) = ∣ inl (refl , adj-refl H u) ∣₁
adj-sym (G BOX H) = PT.rec squash₁ λ where
  (inl (p , e)) → ∣ inl (sym p , adj-sym H e) ∣₁
  (inr (e , p)) → ∣ inr (adj-sym G e , sym p) ∣₁

-- A graph homomorphism is determined by its vertex function.  This
-- lemma matters when writing coherent nerve operators: edge proofs
-- are not additional geometric data.
homExt : {G : Graph ℓ} {H : Graph ℓ'} {f g : Hom G H}
       → ((x : Vertex G) → onVertices f x ≡ onVertices g x) → f ≡ g
onVertices (homExt p i) x = p x i
preserves (homExt {H = H} {f = f} {g = g} p i) {x} {y} e =
  isProp→PathP
    (λ i → adj-isProp H (p x i) (p y i))
    (preserves f e) (preserves g e) i

leftIdentity : {G : Graph ℓ} {H : Graph ℓ'} (f : Hom G H)
             → idHom H ∘g f ≡ f
leftIdentity f = homExt (λ _ → refl)

rightIdentity : {G : Graph ℓ} {H : Graph ℓ'} (f : Hom G H)
              → f ∘g idHom G ≡ f
rightIdentity f = homExt (λ _ → refl)

associativity : {G : Graph ℓ} {H : Graph ℓ'}
                {K : Graph ℓ''} {L : Graph ℓ''}
              → (h : Hom K L) (g : Hom H K) (f : Hom G H)
              → (h ∘g g) ∘g f ≡ h ∘g (g ∘g f)
associativity h g f = homExt (λ _ → refl)
