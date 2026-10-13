{-# OPTIONS --cubical --safe #-}
module DHH.Localization.PowerFunctor where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Cubes using (Position; here; there)
open import DHH.Localization.FreeCategory
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.RigidLocalCongruence
open import DHH.Localization.LevelwiseCore
open import DHH.Localization.ResolutionOperators using (Power)
import DHH.Localization.ResolutionOperators as Res
open RelativeFunctor
private variable ℓ : Level

module _ {C D : Category ℓ ℓ} (F : Functor C D) where
  PowerFunctor : (n : ℕ) → Functor (Power C n) (Power D n)
  Functor.F-ob (PowerFunctor n) = Functor.F-ob F
  Functor.F-hom (PowerFunctor zero) = Functor.F-hom F
  Functor.F-hom (PowerFunctor (suc n)) = Functor.F-hom (FreeFunctor (PowerFunctor n))
  Functor.F-id (PowerFunctor zero) = Functor.F-id F
  Functor.F-id (PowerFunctor (suc n)) = Functor.F-id (FreeFunctor (PowerFunctor n))
  Functor.F-seq (PowerFunctor zero) = Functor.F-seq F
  Functor.F-seq (PowerFunctor (suc n)) = Functor.F-seq (FreeFunctor (PowerFunctor n))

  mutual
    collapseNatural : {n : ℕ} (p : Position (suc n))
      → funcComp (PowerFunctor n) (Res.collapse C p)
        ≡ funcComp (Res.collapse D p) (PowerFunctor (suc n))
    collapseNatural p = Functor≡ (λ _ → refl) (collapseHom p)

    collapseHom : {n : ℕ} (p : Position (suc n)) {x y : Category.ob C}
      (u : Category.Hom[_,_] (Power C (suc n)) x y)
      → Functor.F-hom (funcComp (PowerFunctor n) (Res.collapse C p)) u
        ≡ Functor.F-hom (funcComp (Res.collapse D p) (PowerFunctor (suc n))) u
    collapseHom {n = n} here u i = Functor.F-hom (epsilon-natural (PowerFunctor n) (~ i)) u
    collapseHom {n = suc n} (there p) u =
      (λ i → Functor.F-hom (FreeFunctor-composition (Res.collapse C p)
        (PowerFunctor n) (~ i)) u)
      ∙ (λ i → Functor.F-hom (FreeFunctor (collapseNatural p i)) u)
      ∙ (λ i → Functor.F-hom (FreeFunctor-composition (PowerFunctor (suc n))
        (Res.collapse D p) i) u)

  mutual
    duplicateNatural : {n : ℕ} (p : Position (suc n))
      → funcComp (PowerFunctor (suc (suc n))) (Res.duplicate C p)
        ≡ funcComp (Res.duplicate D p) (PowerFunctor (suc n))
    duplicateNatural p = Functor≡ (λ _ → refl) (duplicateHom p)

    duplicateHom : {n : ℕ} (p : Position (suc n)) {x y : Category.ob C}
      (u : Category.Hom[_,_] (Power C (suc n)) x y)
      → Functor.F-hom (funcComp (PowerFunctor (suc (suc n))) (Res.duplicate C p)) u
        ≡ Functor.F-hom (funcComp (Res.duplicate D p) (PowerFunctor (suc n))) u
    duplicateHom {n = n} here u i = Functor.F-hom (delta-natural (PowerFunctor n) (~ i)) u
    duplicateHom {n = suc n} (there p) u =
      (λ i → Functor.F-hom (FreeFunctor-composition (Res.duplicate C p)
        (PowerFunctor (suc (suc n))) (~ i)) u)
      ∙ (λ i → Functor.F-hom (FreeFunctor (duplicateNatural p i)) u)
      ∙ (λ i → Functor.F-hom (FreeFunctor-composition (PowerFunctor (suc n))
        (Res.duplicate D p) i) u)

