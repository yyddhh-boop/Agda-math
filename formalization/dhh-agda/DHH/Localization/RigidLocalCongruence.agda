{-# OPTIONS --cubical --safe #-}

module DHH.Localization.RigidLocalCongruence where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import DHH.Localization.Ordinary
open import DHH.Localization.OrdinaryEvaluation
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor

open Category
open Functor
open Marking
open RelativeFunctor

private variable ℓ : Level

-- A fixed-object presentation avoids reducing a whole dependent
-- Functor path when only equality of its arrow maps is needed.
record RigidRelativeFunctor {C D : Category ℓ ℓ}
                           (R : Marking C) (S : Marking D)
                           (φ : ob C → ob D) : Type ℓ where
  field
    homR : {x y : ob C} → C [ x , y ] → D [ φ x , φ y ]
    idR : {x : ob C} → homR (id C {x = x}) ≡ id D
    seqR : {x y z : ob C} (f : C [ x , y ]) (g : C [ y , z ])
         → homR (_⋆_ C f g) ≡ _⋆_ D (homR f) (homR g)
    markedR : {x y : ob C} (f : C [ x , y ]) → marked R f → marked S (homR f)
open RigidRelativeFunctor public

asRelative : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
             {φ : ob C → ob D} → RigidRelativeFunctor R S φ → RelativeFunctor R S
F-ob (functor (asRelative {φ = φ} F)) = φ
F-hom (functor (asRelative F)) = homR F
F-id (functor (asRelative F)) = idR F
F-seq (functor (asRelative F)) = seqR F
preservesMarked (asRelative F) = markedR F

rigidify : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
           (F : RelativeFunctor R S) → RigidRelativeFunctor R S (F-ob (functor F))
homR (rigidify F) = F-hom (functor F)
idR (rigidify F) = F-id (functor F)
seqR (rigidify F) = F-seq (functor F)
markedR (rigidify F) = preservesMarked F

abstract
  local-hom-congruence : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
                        {φ : ob C → ob D} (F G : RigidRelativeFunctor R S φ)
                        → ({x y : ob C} (f : C [ x , y ]) → homR F f ≡ homR G f)
                        → {x y : ob C} (u : LocalHom C (marked R) x y)
                        → F-hom (LocalFunctor (asRelative F)) u
                        ≡ F-hom (LocalFunctor (asRelative G)) u
  local-hom-congruence {D = D} {S = S} F G e u =
    sym (unique-on-hom (localBase (asRelative F))
      (localInverts (asRelative F)) K u)
    where
    K : Extension (localBase (asRelative F)) (localInverts (asRelative F))
    Extension.hom K = F-hom (LocalFunctor (asRelative G))
    Extension.hom-id K = F-id (LocalFunctor (asRelative G))
    Extension.hom-compose K = F-seq (LocalFunctor (asRelative G))
    Extension.agrees K f = LocalFunctor-original (asRelative G) f
      ∙ cong (F-hom (canonical D (marked S))) (sym (e f))

  -- The fixed-object universal property also compares a raw relative
  -- functor with its explicit presentation; no Functor eta rule is used.
  rigidify-local-hom : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
                      (F : RelativeFunctor R S) {x y : ob C}
                      (u : LocalHom C (marked R) x y)
                    → F-hom (LocalFunctor (asRelative (rigidify F))) u
                    ≡ F-hom (LocalFunctor F) u
  rigidify-local-hom F u = sym (unique-on-hom
    (localBase (asRelative (rigidify F)))
    (localInverts (asRelative (rigidify F))) K u)
    where
    K : Extension (localBase (asRelative (rigidify F)))
                  (localInverts (asRelative (rigidify F)))
    Extension.hom K = F-hom (LocalFunctor F)
    Extension.hom-id K = F-id (LocalFunctor F)
    Extension.hom-compose K = F-seq (LocalFunctor F)
    Extension.agrees K = LocalFunctor-original F
