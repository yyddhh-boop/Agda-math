{-# OPTIONS --cubical --safe #-}

module DHH.Realization.Simplicial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (isSetℕ)
open import DHH.Topology.Base
open import DHH.Simplicial.Ordinal using (Delta)
open import DHH.Simplicial.Presentation using (DeltaPresentation; presentationEvaluation)
open import DHH.Simplicial.Presented
open import DHH.Realization.Coend

-- A simplex disk diagram is again an EXPLICIT parameter.  It must be
-- instantiated by the standard real topological simplexes to interpret
-- these realized mapping sets in the ordinary homotopy theory of spaces.
module SimplicialRealization {ℓ : Level} (S : DiskDiagram Delta ℓ) where
  D : DiskDiagram DeltaPresentation ℓ
  D = pullbackDisks presentationEvaluation S

  module R (A : PresentedSimplicialSet ℓ) = Realization D (presentedPresheaf A)

  realizeSimplicial : PresentedSimplicialSet ℓ → Top ℓ
  realizeSimplicial A = R.realize A isSetℕ

  realizeSimplicialMap : {A B : PresentedSimplicialSet ℓ}
                       → PresentedNatural A B
                       → Continuous (realizeSimplicial A) (realizeSimplicial B)
  realizeSimplicialMap η = RealizationMap.realizeMap isSetℕ D
    (presentedNaturalTransformation η)
