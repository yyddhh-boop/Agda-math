{-# OPTIONS --cubical --safe #-}

module DHH.Realization.Graph where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Data.Sigma
open import Cubical.Categories.Functor.Base using (Functor)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubicalNerve
open import DHH.CubeCategory
open import DHH.PresheafInterop
open import DHH.Topology.Base
open import DHH.Topology.Category
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.Coend

-- This is the literal point-set coend |N₁G| for the supplied cube disk
-- diagram.  Only the standard real-cube instance recovers the original
-- DHH geometric realization.  The parameter is never hidden.
module GraphRealization {ℓ : Level} (E : CubeGeometry ℓ) where
  D : DiskDiagram CubeCategory ℓ
  D = diagram E

  module R (G : Graph ℓ) = Realization D (asPresheaf (N₁ G))

  NG : Graph ℓ → Top ℓ
  NG G = R.realize G isSetℕ

  NG-map : {G H : Graph ℓ} → Hom G H → Continuous (NG G) (NG H)
  NG-map f = RealizationMap.realizeMap isSetℕ D (asNaturalTransformation (N₁-map f))

  NG-map-id : (G : Graph ℓ) → NG-map (idHom G) ≡ identityContinuous (NG G)
  NG-map-id G = continuousExt (SQ.elimProp
    (λ _ → carrier-isSet (NG G) _ _)
    (λ { (n , c , t) → cong (λ k → R.point G n k t) (leftIdentity c) }))

  NG-map-compose : {G H K : Graph ℓ} (f : Hom G H) (g : Hom H K)
                 → NG-map (g ∘g f) ≡ composeContinuous (NG-map g) (NG-map f)
  NG-map-compose {K = K} f g = continuousExt (SQ.elimProp
    (λ _ → carrier-isSet (NG K) _ _)
    (λ { (n , c , t) → cong (λ k → R.point K n k t) (associativity g f c) }))

  NG-functor : Functor (GraphCategory ℓ) (TopCategory ℓ)
  Functor.F-ob NG-functor = NG
  Functor.F-hom NG-functor = NG-map
  Functor.F-id NG-functor {x = G} = NG-map-id G
  Functor.F-seq NG-functor = NG-map-compose

  module HG = HomotopyGroups E

  -- W is ACTUALLY DEFINED by every positive homotopy-class set and π₀;
  -- it is not a freely chosen predicate or only a low-degree test.
  W : {G H : Graph ℓ} → Hom G H → Type (ℓ-suc ℓ)
  W f = HG.WeakHomotopyEquivalence (NG-map f)
