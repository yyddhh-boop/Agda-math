{-# OPTIONS --cubical --safe #-}

module DHH.Statements.Objects where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (CatIso)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
open import DHH.Graph
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.Graph
open import DHH.Statements.RelativeRealization
open import DHH.Localization.OrdinaryFunctor using (Local)

-- The OBJECT half of DHH: after inverting the actual full weak
-- equivalences, every small topological space is isomorphic to an NG.
-- This is a proposition to prove, not a proof and not the full DHH.
module ObjectStatement {ℓ : Level} (E : CubeGeometry ℓ) where
  module R = GraphRealization E
  module RR = RelativeRealization E

  Represents : Graph ℓ → Top ℓ → Type (ℓ-suc ℓ)
  Represents G X = CatIso (Local RR.topMarking) (R.NG G) X

  ObjectDHH : Type (ℓ-suc ℓ)
  ObjectDHH = (X : Top ℓ) → ∥ Σ[ G ∈ Graph ℓ ] Represents G X ∥₁
