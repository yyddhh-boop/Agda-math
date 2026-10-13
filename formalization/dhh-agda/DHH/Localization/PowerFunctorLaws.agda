{-# OPTIONS --cubical --safe #-}

module DHH.Localization.PowerFunctorLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Localization.FreeCategory
open import DHH.Localization.ResolutionOperators using (Power)
open import DHH.Localization.PowerFunctor using (PowerFunctor)

private variable ℓ : Level

-- These identities strengthen the actual F^n construction.  They do
-- not identify its localized resolution with a classical DK model.
-- The functor paths have a definitionally fixed object component,
-- which permits ordinary hom equalities rather than dependent paths.
module _ (C : Category ℓ ℓ) where
  mutual
    PowerFunctor-identity : (n : ℕ)
      → PowerFunctor (Id {C = C}) n ≡ Id {C = Power C n}
    PowerFunctor-identity n = Functor≡ (λ _ → refl) (PowerFunctor-identity-hom n)

    PowerFunctor-identity-hom : (n : ℕ) {x y : Category.ob C}
      (u : Category.Hom[_,_] (Power C n) x y)
      → Functor.F-hom (PowerFunctor (Id {C = C}) n) u ≡ u
    PowerFunctor-identity-hom zero u = refl
    PowerFunctor-identity-hom (suc n) u =
      (λ i → Functor.F-hom (FreeFunctor (PowerFunctor-identity n i)) u)
      ∙ (λ i → Functor.F-hom (FreeFunctor-identity (Power C n) i) u)

module _ {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E) where
  mutual
    PowerFunctor-composition : (n : ℕ)
      → PowerFunctor (funcComp G F) n
        ≡ funcComp (PowerFunctor G n) (PowerFunctor F n)
    PowerFunctor-composition n = Functor≡ (λ _ → refl) (PowerFunctor-composition-hom n)

    PowerFunctor-composition-hom : (n : ℕ) {x y : Category.ob C}
      (u : Category.Hom[_,_] (Power C n) x y)
      → Functor.F-hom (PowerFunctor (funcComp G F) n) u
        ≡ Functor.F-hom (PowerFunctor G n)
            (Functor.F-hom (PowerFunctor F n) u)
    PowerFunctor-composition-hom zero u = refl
    PowerFunctor-composition-hom (suc n) u =
      (λ i → Functor.F-hom (FreeFunctor (PowerFunctor-composition n i)) u)
      ∙ (λ i → Functor.F-hom
          (FreeFunctor-composition (PowerFunctor F n) (PowerFunctor G n) i) u)
