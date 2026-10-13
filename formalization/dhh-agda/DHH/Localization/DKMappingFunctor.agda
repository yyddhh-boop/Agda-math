{-# OPTIONS --cubical --safe #-}

module DHH.Localization.DKMappingFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Simplicial.Presented
open import DHH.Simplicial.PresentedCategory
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.LevelFunctorLaws
open import DHH.Localization.DKMapping

private variable ℓ : Level

-- Equalities of the whole simplicial maps, including naturality data.
-- This is functoriality of our explicit resolution, not yet its
-- identification with the classical infinity-localization functor.
DKMappingMap-identity : {C : Category ℓ ℓ} (R : Marking C)
  (x y : Category.ob C)
  → DKMappingMap (RelativeIdentity R) x y
    ≡ presentedIdentity (DKMapping R x y)
DKMappingMap-identity R x y = presentedNaturalExt (λ n u → levelIdentityHom R n u)

DKMappingMap-composition : {C D E : Category ℓ ℓ}
  {R : Marking C} {S : Marking D} {T : Marking E}
  (F : RelativeFunctor R S) (G : RelativeFunctor S T)
  (x y : Category.ob C)
  → DKMappingMap (RelativeCompose F G) x y
    ≡ presentedCompose (DKMappingMap F x y)
        (DKMappingMap G (Functor.F-ob (RelativeFunctor.functor F) x)
                        (Functor.F-ob (RelativeFunctor.functor F) y))
DKMappingMap-composition F G x y = presentedNaturalExt (λ n u → levelCompositionHom F G n u)
