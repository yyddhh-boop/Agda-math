{-# OPTIONS --cubical --safe #-}

module DHH.Realization.SimplicialFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Functor.Base using (Functor)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Topology.Base
open import DHH.Topology.Category
open import DHH.Simplicial.Ordinal using (Delta)
open import DHH.Simplicial.Presented
open import DHH.Simplicial.PresentedCategory
open import DHH.Realization.Coend
open import DHH.Realization.Simplicial

-- This functor exists for each supplied disk diagram.  Its functor
-- laws do not assert preservation of products or standard geometry.
module SimplicialRealizationFunctor {ℓ : Level} (S : DiskDiagram Delta ℓ) where
  open SimplicialRealization S

  realizeSimplicial-id : (A : PresentedSimplicialSet ℓ)
    → realizeSimplicialMap (presentedIdentity A)
      ≡ identityContinuous (realizeSimplicial A)
  realizeSimplicial-id A = continuousExt (SQ.elimProp
    (λ _ → carrier-isSet (realizeSimplicial A) _ _)
    (λ { (n , c , t) → refl }))

  realizeSimplicial-compose : {A B C : PresentedSimplicialSet ℓ}
    (f : PresentedNatural A B) (g : PresentedNatural B C)
    → realizeSimplicialMap (presentedCompose f g)
      ≡ composeContinuous (realizeSimplicialMap g) (realizeSimplicialMap f)
  realizeSimplicial-compose {C = C} f g = continuousExt (SQ.elimProp
    (λ _ → carrier-isSet (realizeSimplicial C) _ _)
    (λ { (n , c , t) → refl }))

  realizeSimplicial-functor : Functor (PresentedSimplicialSetCategory ℓ) (TopCategory ℓ)
  Functor.F-ob realizeSimplicial-functor = realizeSimplicial
  Functor.F-hom realizeSimplicial-functor = realizeSimplicialMap
  Functor.F-id realizeSimplicial-functor {x = A} = realizeSimplicial-id A
  Functor.F-seq realizeSimplicial-functor = realizeSimplicial-compose
