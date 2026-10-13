{-# OPTIONS --cubical --safe #-}
module DHH.Localization.ResolutionFunctorCore where
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
open import DHH.Localization.PowerFunctor public
private variable ℓ : Level

module _ {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
         (F : RelativeFunctor R S) where
  PowerRelativeFunctor : (n : ℕ) → RelativeFunctor (PowerMarking R n) (PowerMarking S n)
  functor (PowerRelativeFunctor n) = PowerFunctor (functor F) n
  preservesMarked (PowerRelativeFunctor zero) = preservesMarked F
  preservesMarked (PowerRelativeFunctor (suc n)) = preservesMarked (FreeRelativeFunctor (PowerRelativeFunctor n))

  LevelFunctor : (n : ℕ) → Functor (LocalizedResolution R n) (LocalizedResolution S n)
  LevelFunctor n = LocalFunctor (PowerRelativeFunctor (suc n))

