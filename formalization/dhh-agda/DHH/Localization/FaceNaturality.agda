{-# OPTIONS --cubical --safe #-}
module DHH.Localization.FaceNaturality where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Cubes using (Position; here; there)
open import DHH.Localization.FreeCategory
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.OrdinaryEvaluation
open import DHH.Localization.ExtensionComparison
open import DHH.Localization.Ordinary using (canonical)
open import DHH.Localization.RigidLocalCongruence
open import DHH.Localization.LevelwiseCore
open import DHH.Localization.ResolutionOperators using (Power)
import DHH.Localization.ResolutionOperators as Res
open RelativeFunctor
open import DHH.Localization.PowerFunctor public
open import DHH.Localization.ResolutionFunctorCore public
private variable ℓ : Level

module _ {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
         (F : RelativeFunctor R S) where
  faceNaturalHom : {n : ℕ} (p : Position (suc (suc n)))
    {x y : Category.ob C} (u : MappingSimplex R x y (suc n))
    → Functor.F-hom (LevelFunctor F n) (Functor.F-hom (face R p) u)
      ≡ Functor.F-hom (face S p) (Functor.F-hom (LevelFunctor F (suc n)) u)
  faceNaturalHom {n = n} p u = compareExtensions
    {C = Power C (suc (suc n))}
    {W = Marking.marked (PowerMarking R (suc (suc n)))}
    {D = LocalizedPower S (suc n)}
    base inverted left right u
    where
    A : RelativeFunctor (PowerMarking R (suc (suc n))) (PowerMarking R (suc n))
    A = collapseRelative R p
    B : RelativeFunctor (PowerMarking R (suc n)) (PowerMarking S (suc n))
    B = PowerRelativeFunctor F (suc n)
    A' : RelativeFunctor (PowerMarking R (suc (suc n))) (PowerMarking S (suc (suc n)))
    A' = PowerRelativeFunctor F (suc (suc n))
    B' : RelativeFunctor (PowerMarking S (suc (suc n))) (PowerMarking S (suc n))
    B' = collapseRelative S p

    base : Functor (Power C (suc (suc n))) (LocalizedPower S (suc n))
    base = localBase (RelativeCompose A B)
    inverted : {x y : Category.ob C} (v : Category.Hom[_,_] (Power C (suc (suc n))) x y)
      → Marking.marked (PowerMarking R (suc (suc n))) v
      → Cubical.Categories.Category.Base.isIso (LocalizedPower S (suc n)) (Functor.F-hom base v)
    inverted = localInverts (RelativeCompose A B)

    left : Extension base inverted
    Extension.hom left v = Functor.F-hom (LocalFunctor B) (Functor.F-hom (LocalFunctor A) v)
    Extension.hom-id left = cong (Functor.F-hom (LocalFunctor B)) (Functor.F-id (LocalFunctor A))
      ∙ Functor.F-id (LocalFunctor B)
    Extension.hom-compose left v w =
      cong (Functor.F-hom (LocalFunctor B)) (Functor.F-seq (LocalFunctor A) v w)
      ∙ Functor.F-seq (LocalFunctor B)
          (Functor.F-hom (LocalFunctor A) v) (Functor.F-hom (LocalFunctor A) w)
    Extension.agrees left v =
      cong (Functor.F-hom (LocalFunctor B)) (LocalFunctor-original A v)
      ∙ LocalFunctor-original B (Functor.F-hom (functor A) v)

    right : Extension base inverted
    Extension.hom right v = Functor.F-hom (LocalFunctor B') (Functor.F-hom (LocalFunctor A') v)
    Extension.hom-id right = cong (Functor.F-hom (LocalFunctor B')) (Functor.F-id (LocalFunctor A'))
      ∙ Functor.F-id (LocalFunctor B')
    Extension.hom-compose right v w =
      cong (Functor.F-hom (LocalFunctor B')) (Functor.F-seq (LocalFunctor A') v w)
      ∙ Functor.F-seq (LocalFunctor B')
          (Functor.F-hom (LocalFunctor A') v) (Functor.F-hom (LocalFunctor A') w)
    Extension.agrees right v =
      cong (Functor.F-hom (LocalFunctor B')) (LocalFunctor-original A' v)
      ∙ LocalFunctor-original B' (Functor.F-hom (functor A') v)
      ∙ cong (Functor.F-hom (canonical (Power D (suc n))
          (Marking.marked (PowerMarking S (suc n)))))
          (sym (collapseHom (functor F) p v))

