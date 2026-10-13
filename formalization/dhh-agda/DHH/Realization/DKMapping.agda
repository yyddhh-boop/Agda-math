{-# OPTIONS --cubical --safe #-}

module DHH.Realization.DKMapping where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Topology.Base
open import DHH.Simplicial.Ordinal using (Delta)
open import DHH.Realization.Coend using (DiskDiagram)
open import DHH.Realization.Simplicial
open import DHH.Realization.SimplicialFunctor
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.DKMapping
open import DHH.Localization.DKMappingFunctor

-- Actual spaces and continuous maps, functorial in a relative functor.
-- Standard geometry and comparison to classical DK remain separate.
-- In particular, this does not assert that realization preserves the
-- product needed for a continuous composition of mapping spaces.
module RealizedDKMapping {ℓ : Level} (S : DiskDiagram Delta ℓ) where
  open SimplicialRealization S
  open SimplicialRealizationFunctor S

  MappingSpace : {C : Category ℓ ℓ} (R : Marking C)
    → Category.ob C → Category.ob C → Top ℓ
  MappingSpace R x y = realizeSimplicial (DKMapping R x y)

  mappingMap : {C D : Category ℓ ℓ} {R : Marking C} {T : Marking D}
    (F : RelativeFunctor R T) (x y : Category.ob C)
    → Continuous (MappingSpace R x y)
        (MappingSpace T (Functor.F-ob (RelativeFunctor.functor F) x)
                        (Functor.F-ob (RelativeFunctor.functor F) y))
  mappingMap F x y = realizeSimplicialMap (DKMappingMap F x y)

  mappingMap-identity : {C : Category ℓ ℓ} (R : Marking C)
    (x y : Category.ob C)
    → mappingMap (RelativeIdentity R) x y ≡ identityContinuous (MappingSpace R x y)
  mappingMap-identity R x y =
    cong realizeSimplicialMap (DKMappingMap-identity R x y)
    ∙ realizeSimplicial-id (DKMapping R x y)

  mappingMap-composition : {C D E : Category ℓ ℓ}
    {R : Marking C} {T : Marking D} {U : Marking E}
    (F : RelativeFunctor R T) (G : RelativeFunctor T U)
    (x y : Category.ob C)
    → mappingMap (RelativeCompose F G) x y
      ≡ composeContinuous
          (mappingMap G (Functor.F-ob (RelativeFunctor.functor F) x)
                        (Functor.F-ob (RelativeFunctor.functor F) y))
          (mappingMap F x y)
  mappingMap-composition F G x y =
    cong realizeSimplicialMap (DKMappingMap-composition F G x y)
    ∙ realizeSimplicial-compose (DKMappingMap F x y)
        (DKMappingMap G (Functor.F-ob (RelativeFunctor.functor F) x)
                        (Functor.F-ob (RelativeFunctor.functor F) y))
