{-# OPTIONS --cubical --safe #-}

module DHH.GraphSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import DHH.Graph

private
  variable ℓ ℓ' : Level

Preserves : (G : Graph ℓ) (H : Graph ℓ')
          → (Vertex G → Vertex H) → Type (ℓ-max ℓ ℓ')
Preserves G H f = (x y : Vertex G) → Adj G x y → Adj H (f x) (f y)

preserves-isProp : (G : Graph ℓ) (H : Graph ℓ')
                  (f : Vertex G → Vertex H) → isProp (Preserves G H f)
preserves-isProp G H f = isPropΠ3 (λ x y _ → adj-isProp H (f x) (f y))

HomΣ : (G : Graph ℓ) (H : Graph ℓ') → Type (ℓ-max ℓ ℓ')
HomΣ G H = Σ[ f ∈ (Vertex G → Vertex H) ] Preserves G H f

homToΣ : {G : Graph ℓ} {H : Graph ℓ'} → Hom G H → HomΣ G H
homToΣ f = onVertices f , λ x y e → preserves f e

ΣToHom : {G : Graph ℓ} {H : Graph ℓ'} → HomΣ G H → Hom G H
onVertices (ΣToHom (f , p)) = f
preserves (ΣToHom (f , p)) {x} {y} e = p x y e

isSetGraphHom : {G : Graph ℓ} {H : Graph ℓ'} → isSet (Hom G H)
isSetGraphHom {G = G} {H = H} =
  isSetRetract homToΣ ΣToHom (λ f → homExt (λ _ → refl))
    (isSetΣSndProp (isSetΠ (λ _ → vertex-isSet H))
      (preserves-isProp G H))

GraphCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (GraphCategory ℓ) = Graph ℓ
Category.Hom[_,_] (GraphCategory ℓ) = Hom
Category.id (GraphCategory ℓ) {x = G} = idHom G
Category._⋆_ (GraphCategory ℓ) f g = g ∘g f
Category.⋆IdL (GraphCategory ℓ) = rightIdentity
Category.⋆IdR (GraphCategory ℓ) = leftIdentity
Category.⋆Assoc (GraphCategory ℓ) f g h = sym (associativity h g f)
Category.isSetHom (GraphCategory ℓ) = isSetGraphHom
