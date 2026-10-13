{-# OPTIONS --cubical --safe #-}

module DHH.Localization.OrdinaryFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import DHH.Localization.Zigzag
open import DHH.Localization.Ordinary
open import DHH.Localization.OrdinaryEvaluation
open import DHH.Localization.RelativeFree

open Category
open Functor
open Marking
open RelativeFunctor

private variable ℓ : Level

Local : {C : Category ℓ ℓ} → Marking C → Category ℓ ℓ
Local {C = C} R = OrdinaryLocalization C (marked R)

module _ {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
         (F : RelativeFunctor R S) where

  localBase : Functor C (Local S)
  localBase = funcComp (canonical D (marked S)) (functor F)

  localInverts : {x y : ob C} (f : C [ x , y ]) → marked R f
                → isIso (Local S) (F-hom localBase f)
  localInverts f w = markedIsIso D (marked S) (F-hom (functor F) f)
    (preservesMarked F f w)

  LocalFunctor : Functor (Local R) (Local S)
  LocalFunctor = extension localBase localInverts

  LocalFunctor-original : {x y : ob C} (f : C [ x , y ])
                         → F-hom LocalFunctor (F-hom (canonical C (marked R)) f)
                           ≡ F-hom (canonical D (marked S)) (F-hom (functor F) f)
  LocalFunctor-original = extension-on-arrow localBase localInverts

RelativeIdentity : {C : Category ℓ ℓ} (R : Marking C) → RelativeFunctor R R
functor (RelativeIdentity R) = Id
preservesMarked (RelativeIdentity R) f w = w

RelativeCompose : {C D E : Category ℓ ℓ}
                  {R : Marking C} {S : Marking D} {T : Marking E}
                → RelativeFunctor R S → RelativeFunctor S T → RelativeFunctor R T
functor (RelativeCompose F G) = funcComp (functor G) (functor F)
preservesMarked (RelativeCompose F G) f w =
  preservesMarked G (F-hom (functor F) f) (preservesMarked F f w)

RelativeFunctorPath : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
                     {F G : RelativeFunctor R S}
                   → functor F ≡ functor G → F ≡ G
functor (RelativeFunctorPath p i) = p i
preservesMarked (RelativeFunctorPath {S = S} {F = F} {G = G} p i) f w =
  isProp→PathP (λ j → marked-isProp S (F-hom (p j) f))
    (preservesMarked F f w) (preservesMarked G f w) i

LocalFunctor-identity : {C : Category ℓ ℓ} (R : Marking C)
                      → LocalFunctor (RelativeIdentity R) ≡ Id
LocalFunctor-identity {C = C} R = Functor≡ (λ _ → refl)
  (λ u → sym (unique-on-hom (localBase (RelativeIdentity R))
    (localInverts (RelativeIdentity R)) identityExtension u))
  where
  identityExtension : Extension (localBase (RelativeIdentity R))
    (localInverts (RelativeIdentity R))
  Extension.hom identityExtension u = u
  Extension.hom-id identityExtension = refl
  Extension.hom-compose identityExtension u v = refl
  Extension.agrees identityExtension f = refl

LocalFunctor-composition : {C D E : Category ℓ ℓ}
                          {R : Marking C} {S : Marking D} {T : Marking E}
                        → (F : RelativeFunctor R S) (G : RelativeFunctor S T)
                        → LocalFunctor (RelativeCompose F G)
                          ≡ funcComp (LocalFunctor G) (LocalFunctor F)
LocalFunctor-composition {C = C} {R = R} F G = Functor≡ (λ _ → refl)
  (λ u → sym (unique-on-hom (localBase (RelativeCompose F G))
    (localInverts (RelativeCompose F G)) compositionExtension u))
  where
  K = funcComp (LocalFunctor G) (LocalFunctor F)
  compositionExtension : Extension (localBase (RelativeCompose F G))
    (localInverts (RelativeCompose F G))
  Extension.hom compositionExtension = F-hom K
  Extension.hom-id compositionExtension = F-id K
  Extension.hom-compose compositionExtension = F-seq K
  Extension.agrees compositionExtension f =
    cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
    ∙ LocalFunctor-original G (F-hom (functor F) f)

abstract
  LocalFunctor-composition-hom : {C D E : Category ℓ ℓ}
      {R : Marking C} {S : Marking D} {T : Marking E}
      (F : RelativeFunctor R S) (G : RelativeFunctor S T)
      {x y : ob C} (u : LocalHom C (marked R) x y)
    → F-hom (LocalFunctor (RelativeCompose F G)) u
      ≡ F-hom (LocalFunctor G) (F-hom (LocalFunctor F) u)
  LocalFunctor-composition-hom F G u i =
    F-hom (LocalFunctor-composition F G i) u

  LocalFunctor-identity-hom : {C : Category ℓ ℓ} (R : Marking C)
      {x y : ob C} (u : LocalHom C (marked R) x y)
    → F-hom (LocalFunctor (RelativeIdentity R)) u ≡ u
  LocalFunctor-identity-hom R u i = F-hom (LocalFunctor-identity R i) u

abstract
  LocalFunctor-path-hom : {C D : Category ℓ ℓ}
      {R : Marking C} {S : Marking D}
      {F G : RelativeFunctor R S} (p : F ≡ G)
      {x y : ob C} (u : LocalHom C (marked R) x y)
    → PathP (λ i → Local S [ F-ob (functor (p i)) x , F-ob (functor (p i)) y ])
        (F-hom (LocalFunctor F) u) (F-hom (LocalFunctor G) u)
  LocalFunctor-path-hom p u i = F-hom (LocalFunctor (p i)) u

-- Lift a commuting square all at once.  Its object path is taken
-- directly from the original square, so a rigid square stays rigid.
abstract
  LocalFunctor-square-hom : {C A B D : Category ℓ ℓ}
      {R : Marking C} {P : Marking A} {Q : Marking B} {S : Marking D}
      (F : RelativeFunctor R P) (G : RelativeFunctor P S)
      (F' : RelativeFunctor R Q) (G' : RelativeFunctor Q S)
      (p : functor (RelativeCompose F G) ≡ functor (RelativeCompose F' G'))
      {x y : ob C} (u : LocalHom C (marked R) x y)
    → PathP (λ i → Local S [ F-ob (p i) x , F-ob (p i) y ])
        (F-hom (LocalFunctor G) (F-hom (LocalFunctor F) u))
        (F-hom (LocalFunctor G') (F-hom (LocalFunctor F') u))
  LocalFunctor-square-hom {C = C} {D = D} {R = R} {S = S} F G F' G' p u i =
    hcomp (λ j → λ { (i = i0) → LocalFunctor-composition-hom F G u j
                   ; (i = i1) → LocalFunctor-composition-hom F' G' u j })
      (LocalFunctor-path-hom
        (RelativeFunctorPath {C = C} {D = D} {R = R} {S = S}
          {F = RelativeCompose F G} {G = RelativeCompose F' G'} p) u i)
