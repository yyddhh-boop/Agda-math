{-# OPTIONS --cubical --safe #-}
module DHH.Localization.ExtensionComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import DHH.Localization.Ordinary
open import DHH.Localization.OrdinaryEvaluation
open Category
open Functor
private variable ℓo ℓh ℓw ℓdo ℓdh : Level

abstract
  compareExtensions : {C : Category ℓo ℓh}
    {W : {x y : ob C} → C [ x , y ] → Type ℓw}
    {D : Category ℓdo ℓdh}
    (F : Functor C D)
    (inverts : {x y : ob C} (f : C [ x , y ]) → W f → isIso D (F-hom F f))
    (K L : Extension F inverts) {x y : ob C} (u : LocalHom C W x y)
    → Extension.hom K u ≡ Extension.hom L u
  compareExtensions F inverts K L u =
    unique-on-hom F inverts K u ∙ sym (unique-on-hom F inverts L u)
