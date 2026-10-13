{-# OPTIONS --cubical --safe #-}

module DHH.Localization.RelativeFree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.UnderlyingGraph using (Cat→Graph)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.Categories.Constructions.Free.Category.Base as LibraryFree
open import DHH.Localization.FreeCategory

open Category
open Functor

private variable ℓ : Level

-- A wide subcategory of marked arrows.  The closure laws are genuine
-- data, not assertions that an arbitrary class is a relative category.
record Marking (C : Category ℓ ℓ) : Type (ℓ-suc ℓ) where
  field
    marked : {x y : ob C} → C [ x , y ] → Type ℓ
    marked-isProp : {x y : ob C} (f : C [ x , y ]) → isProp (marked f)
    marked-id : {x : ob C} → marked (id C {x = x})
    marked-compose : {x y z : ob C} (f : C [ x , y ]) (g : C [ y , z ])
                   → marked f → marked g → marked (_⋆_ C f g)

open Marking

MarkedCategory : {C : Category ℓ ℓ} → Marking C → Category ℓ ℓ
ob (MarkedCategory {C = C} R) = ob C
Hom[_,_] (MarkedCategory {C = C} R) x y = Σ[ f ∈ C [ x , y ] ] marked R f
id (MarkedCategory {C = C} R) = id C , marked-id R
_⋆_ (MarkedCategory {C = C} R) (f , p) (g , q) =
  _⋆_ C f g , marked-compose R f g p q
⋆IdL (MarkedCategory {C = C} R) f = Σ≡Prop (marked-isProp R) (⋆IdL C (fst f))
⋆IdR (MarkedCategory {C = C} R) f = Σ≡Prop (marked-isProp R) (⋆IdR C (fst f))
⋆Assoc (MarkedCategory {C = C} R) f g h =
  Σ≡Prop (marked-isProp R) (⋆Assoc C (fst f) (fst g) (fst h))
isSetHom (MarkedCategory {C = C} R) = isSetΣSndProp (isSetHom C) (marked-isProp R)

inclusion : {C : Category ℓ ℓ} (R : Marking C) → Functor (MarkedCategory R) C
F-ob (inclusion R) x = x
F-hom (inclusion R) = fst
F-id (inclusion R) = refl
F-seq (inclusion R) f g = refl

record RelativeFunctor {C D : Category ℓ ℓ} (R : Marking C) (S : Marking D)
                       : Type ℓ where
  field
    functor : Functor C D
    preservesMarked : {x y : ob C} (f : C [ x , y ])
                    → marked R f → marked S (F-hom functor f)

open RelativeFunctor

markedFunctor : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
              → RelativeFunctor R S → Functor (MarkedCategory R) (MarkedCategory S)
F-ob (markedFunctor F) = F-ob (functor F)
F-hom (markedFunctor F) (f , w) = F-hom (functor F) f , preservesMarked F f w
F-id (markedFunctor {S = S} F) = Σ≡Prop (marked-isProp S) (F-id (functor F))
F-seq (markedFunctor {S = S} F) f g =
  Σ≡Prop (marked-isProp S) (F-seq (functor F) (fst f) (fst g))

-- Free marked words are exactly the propositional image of F(W) in
-- F(C).  This is stricter than merely asking whether epsilon(word)
-- belongs to W: every generator of the word must come from W.
FreeMarked : {C : Category ℓ ℓ} (R : Marking C) {x y : ob C}
           → Free C [ x , y ] → Type ℓ
FreeMarked R f = ∥ Σ[ u ∈ Free (MarkedCategory R) [ _ , _ ] ]
                    F-hom (FreeFunctor (inclusion R)) u ≡ f ∥₁

FreeMarking : {C : Category ℓ ℓ} → Marking C → Marking (Free C)
marked (FreeMarking R) = FreeMarked R
marked-isProp (FreeMarking R) _ = squash₁
marked-id (FreeMarking R) = ∣ id (Free (MarkedCategory R)) , F-id (FreeFunctor (inclusion R)) ∣₁
marked-compose (FreeMarking {C = C} R) f g = PT.rec (isPropΠ (λ _ → squash₁))
  (λ where (u , p) → PT.rec squash₁ λ where
     (v , q) → ∣ _⋆_ (Free (MarkedCategory R)) u v ,
       F-seq (FreeFunctor (inclusion R)) u v ∙ cong₂ (_⋆_ (Free C)) p q ∣₁)

FreeRelativeFunctor : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
                    → RelativeFunctor R S → RelativeFunctor (FreeMarking R) (FreeMarking S)
functor (FreeRelativeFunctor F) = FreeFunctor (functor F)
preservesMarked (FreeRelativeFunctor {C = C} {D = D} {R = R} {S = S} F) f =
  PT.rec squash₁ (λ where
    (u , p) → ∣ F-hom (FreeFunctor (markedFunctor F)) u ,
      cong (λ K → F-hom K u) square
      ∙ cong (F-hom (FreeFunctor (functor F))) p ∣₁)
  where
  square : funcComp (FreeFunctor (inclusion S)) (FreeFunctor (markedFunctor F))
           ≡ funcComp (FreeFunctor (functor F)) (FreeFunctor (inclusion R))
  square = LibraryFree.FreeCategory.induction (Cat→Graph (MarkedCategory R)) _ _ refl

epsilonRelative : {C : Category ℓ ℓ} (R : Marking C)
                → RelativeFunctor (FreeMarking R) R
functor (epsilonRelative {C = C} R) = epsilon C
preservesMarked (epsilonRelative {C = C} R) f = PT.rec (marked-isProp R _) λ where
  (u , p) → subst (marked R)
    (sym (cong (λ F → F-hom F u) (epsilon-natural (inclusion R)))
      ∙ cong (F-hom (epsilon C)) p)
    (snd (F-hom (epsilon (MarkedCategory R)) u))

-- F(W) embeds in the marked subcategory of F(C).
liftMarkedWords : {C : Category ℓ ℓ} (R : Marking C)
                → Functor (Free (MarkedCategory R)) (MarkedCategory (FreeMarking R))
F-ob (liftMarkedWords R) x = x
F-hom (liftMarkedWords R) u = F-hom (FreeFunctor (inclusion R)) u , ∣ u , refl ∣₁
F-id (liftMarkedWords R) = Σ≡Prop (λ _ → squash₁) (F-id (FreeFunctor (inclusion R)))
F-seq (liftMarkedWords R) u v =
  Σ≡Prop (λ _ → squash₁) (F-seq (FreeFunctor (inclusion R)) u v)

deltaRelative : {C : Category ℓ ℓ} (R : Marking C)
              → RelativeFunctor (FreeMarking R) (FreeMarking (FreeMarking R))
functor (deltaRelative {C = C} R) = delta C
preservesMarked (deltaRelative {C = C} R) f = PT.rec squash₁ (λ where
  (u , p) → ∣ F-hom (FreeFunctor (liftMarkedWords R)) (F-hom (delta (MarkedCategory R)) u) ,
    cong (λ F → F-hom F u) square ∙ cong (F-hom (delta C)) p ∣₁)
  where
  square : funcComp (FreeFunctor (inclusion (FreeMarking R)))
                    (funcComp (FreeFunctor (liftMarkedWords R)) (delta (MarkedCategory R)))
           ≡ funcComp (delta C) (FreeFunctor (inclusion R))
  square = LibraryFree.FreeCategory.induction (Cat→Graph (MarkedCategory R)) _ _ refl
