{-# OPTIONS --cubical --safe #-}

module DHH.Localization.LevelFunctorLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Localization.RelativeFree
open import DHH.Localization.Ordinary using (canonical)
open import DHH.Localization.OrdinaryEvaluation
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.ResolutionOperators using (Power)
open import DHH.Localization.PowerFunctorLaws
open import DHH.Localization.LevelwiseCore
open import DHH.Localization.ResolutionFunctorCore

open RelativeFunctor
private variable ℓ : Level

-- The object maps of Power and LevelFunctor are definitionally fixed.
-- We compare extensions on homs directly, rather than transporting
-- through equality of the whole dependent Functor record.
module _ {C : Category ℓ ℓ} (R : Marking C) where
  levelIdentityHom : (n : ℕ) {x y : Category.ob C}
    (u : MappingSimplex R x y n)
    → Functor.F-hom (LevelFunctor (RelativeIdentity R) n) u ≡ u
  levelIdentityHom n u = sym (unique-on-hom
    (localBase A) (localInverts A) identityExtension u)
    where
    A : RelativeFunctor (PowerMarking R (suc n)) (PowerMarking R (suc n))
    A = PowerRelativeFunctor (RelativeIdentity R) (suc n)

    identityExtension : Extension (localBase A) (localInverts A)
    Extension.hom identityExtension v = v
    Extension.hom-id identityExtension = refl
    Extension.hom-compose identityExtension v w = refl
    Extension.agrees identityExtension v = sym
      (cong (Functor.F-hom (canonical (Power C (suc n))
        (Marking.marked (PowerMarking R (suc n)))))
        (PowerFunctor-identity-hom C (suc n) v))

module _ {C D E : Category ℓ ℓ}
         {R : Marking C} {S : Marking D} {T : Marking E}
         (F : RelativeFunctor R S) (G : RelativeFunctor S T) where
  levelCompositionHom : (n : ℕ) {x y : Category.ob C}
    (u : MappingSimplex R x y n)
    → Functor.F-hom (LevelFunctor (RelativeCompose F G) n) u
      ≡ Functor.F-hom (LevelFunctor G n)
          (Functor.F-hom (LevelFunctor F n) u)
  levelCompositionHom n u = sym (unique-on-hom
    (localBase A) (localInverts A) compositionExtension u)
    where
    A : RelativeFunctor (PowerMarking R (suc n)) (PowerMarking T (suc n))
    A = PowerRelativeFunctor (RelativeCompose F G) (suc n)

    compositionExtension : Extension (localBase A) (localInverts A)
    Extension.hom compositionExtension v = Functor.F-hom (LevelFunctor G n)
      (Functor.F-hom (LevelFunctor F n) v)
    Extension.hom-id compositionExtension =
      cong (Functor.F-hom (LevelFunctor G n)) (Functor.F-id (LevelFunctor F n))
      ∙ Functor.F-id (LevelFunctor G n)
    Extension.hom-compose compositionExtension v w =
      cong (Functor.F-hom (LevelFunctor G n)) (Functor.F-seq (LevelFunctor F n) v w)
      ∙ Functor.F-seq (LevelFunctor G n)
          (Functor.F-hom (LevelFunctor F n) v) (Functor.F-hom (LevelFunctor F n) w)
    Extension.agrees compositionExtension v =
      cong (Functor.F-hom (LevelFunctor G n))
        (LocalFunctor-original (PowerRelativeFunctor F (suc n)) v)
      ∙ LocalFunctor-original (PowerRelativeFunctor G (suc n))
          (Functor.F-hom (PowerFunctor (functor F) (suc n)) v)
      ∙ sym (cong (Functor.F-hom (canonical (Power E (suc n))
          (Marking.marked (PowerMarking T (suc n)))))
          (PowerFunctor-composition-hom (functor F) (functor G) (suc n) v))
