{-# OPTIONS --cubical --safe #-}

module DHH.Localization.LevelwiseCore where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Cubes using (Position; here; there; weakenPosition;
  CoordinatePair; front; under; lower; upper; lowerWide; upperWide)
open import DHH.Localization.FreeCategory
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.ResolutionOperators using (Power)
import DHH.Localization.ResolutionOperators as Res

open RelativeFunctor

private variable ℓ : Level

module _ {C : Category ℓ ℓ} (R : Marking C) where

  PowerMarking : (n : ℕ) → Marking (Power C n)
  PowerMarking zero = R
  PowerMarking (suc n) = FreeMarking (PowerMarking n)

  collapseRelative : {n : ℕ} → Position (suc n)
                   → RelativeFunctor (PowerMarking (suc n)) (PowerMarking n)
  functor (collapseRelative i) = Res.collapse C i
  preservesMarked (collapseRelative {n = n} here) =
    preservesMarked (epsilonRelative (PowerMarking n))
  preservesMarked (collapseRelative {n = suc n} (there i)) =
    preservesMarked (FreeRelativeFunctor (collapseRelative i))

  duplicateRelative : {n : ℕ} → Position (suc n)
                    → RelativeFunctor (PowerMarking (suc n)) (PowerMarking (suc (suc n)))
  functor (duplicateRelative i) = Res.duplicate C i
  preservesMarked (duplicateRelative {n = n} here) =
    preservesMarked (deltaRelative (PowerMarking n))
  preservesMarked (duplicateRelative {n = suc n} (there i)) =
    preservesMarked (FreeRelativeFunctor (duplicateRelative i))

  collapse-underlying : {n : ℕ} (i : Position (suc n))
                       → functor (collapseRelative i) ≡ Res.collapse C i
  collapse-underlying i = refl

  duplicate-underlying : {n : ℕ} (i : Position (suc n))
                        → functor (duplicateRelative i) ≡ Res.duplicate C i
  duplicate-underlying i = refl

  LocalizedPower : ℕ → Category ℓ ℓ
  LocalizedPower n = Local (PowerMarking n)

  -- These are actual mapping SETS in each degree of a free resolution.
  -- The simplicial direction, subsequently realized, retains homotopies;
  -- a single degree is not an infinity-localization mapping space.
  LocalizedResolution : ℕ → Category ℓ ℓ
  LocalizedResolution n = LocalizedPower (suc n)

  MappingSimplex : (x y : Category.ob C) → ℕ → Type ℓ
  MappingSimplex x y n = Category.Hom[_,_] (LocalizedResolution n) x y

  localCollapse : {n : ℕ} → Position (suc n)
                → Functor (LocalizedPower (suc n)) (LocalizedPower n)
  localCollapse i = LocalFunctor (collapseRelative i)

  localDuplicate : {n : ℕ} → Position (suc n)
                 → Functor (LocalizedPower (suc n)) (LocalizedPower (suc (suc n)))
  localDuplicate i = LocalFunctor (duplicateRelative i)

  face : {n : ℕ} → Position (suc (suc n))
       → Functor (LocalizedResolution (suc n)) (LocalizedResolution n)
  face = localCollapse

  degeneracy : {n : ℕ} → Position (suc n)
             → Functor (LocalizedResolution n) (LocalizedResolution (suc n))
  degeneracy = localDuplicate

