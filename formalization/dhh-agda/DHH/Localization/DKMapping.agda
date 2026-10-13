{-# OPTIONS --cubical --safe #-}

module DHH.Localization.DKMapping where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Simplicial.Presented
open import DHH.Localization.RelativeFree
open import DHH.Localization.LevelwiseCore
import DHH.Localization.RigidLevelwiseLaws as Laws
open import DHH.Localization.LevelwiseFunctor

private variable ℓ : Level

-- The free-category comonad used here retains identity arrows as
-- generators.  This is an explicitly constructed variant of the
-- Dwyer--Kan free resolution, not the literal nonidentity-generator
-- definition in the original paper.  Comparison with an infinity
-- localization is a separate theorem, not an axiom of this module.
DKMapping : {C : Category ℓ ℓ} (R : Marking C)
          → Category.ob C → Category.ob C → PresentedSimplicialSet ℓ
cellsP (DKMapping R x y) n = MappingSimplex R x y n , Category.isSetHom (LocalizedResolution R n)
faceP (DKMapping R x y) p = Functor.F-hom (face R p)
degenP (DKMapping R x y) p = Functor.F-hom (degeneracy R p)
facesP (DKMapping R x y) p c = Laws.facesHom R p c
degensP (DKMapping R x y) p c = Laws.degensHom R p c
sameP (DKMapping R x y) p c = Laws.sameHom R p c
nextP (DKMapping R x y) p c = Laws.nextHom R p c
beforeP (DKMapping R x y) p c = Laws.beforeHom R p c
afterP (DKMapping R x y) p c = Laws.afterHom R p c

DKMappingMap : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
             → (F : RelativeFunctor R S) (x y : Category.ob C)
             → PresentedNatural (DKMapping R x y)
                 (DKMapping S (Functor.F-ob (RelativeFunctor.functor F) x)
                              (Functor.F-ob (RelativeFunctor.functor F) y))
mapPCell (DKMappingMap F x y) n = Functor.F-hom (LevelFunctor F n)
face-naturalP (DKMappingMap F x y) p c = faceNaturalHom F p c
degen-naturalP (DKMappingMap F x y) p c = degeneracyNaturalHom F p c
