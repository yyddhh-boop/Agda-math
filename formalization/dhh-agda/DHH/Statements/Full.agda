{-# OPTIONS --cubical --safe #-}

module DHH.Statements.Full where

open import Cubical.Foundations.Prelude
open import DHH.Graph
open import DHH.Topology.Base
open import DHH.Topology.Category using (TopCategory)
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.Coend using (DiskDiagram)
open import DHH.Realization.Graph
open import DHH.Realization.DKMapping
open import DHH.Simplicial.Ordinal using (Delta)
open import DHH.Statements.RelativeRealization
open import DHH.Statements.Objects
open import DHH.Localization.DKEnrichment using
  (PresentedEnrichedCategory; PresentedEnrichedFunctor; DKEnrichedCategory; DKEnrichedFunctor)

-- THREE explicit geometry inputs:
--   E     : cubes for the small topological spaces NG and their W;
--   S     : higher-universe simplexes for the derived mapping sets;
--   E-map : matching higher-universe cubes for weak-equivalence tests.
-- For the original DHH, these MUST be compatible STANDARD real models.
-- Geometry.RealCubeDiagram, RealCubeLift and RealSimplexLift construct
-- those instances; Statements.Concrete fixes them with no geometry
-- parameters.  An arbitrary triple does not give the original conjecture.
--
-- The mapping objects and comparison are nevertheless ACTUAL checked
-- constructions from the relative NG functor, not arbitrary fields
-- asking the reader to supply the desired mapping spaces.
module Statement {ℓ : Level}
                 (E : CubeGeometry ℓ)
                 (S : DiskDiagram Delta (ℓ-suc ℓ))
                 (E-map : CubeGeometry (ℓ-suc ℓ)) where
  module R = GraphRealization E
  module RR = RelativeRealization E
  module M = RealizedDKMapping S
  module HG-map = HomotopyGroups E-map
  module O = ObjectStatement E

  -- The candidate mapping objects also have genuine simplicial
  -- composition and units, and NG preserves those operations.
  -- This does not assert Kan fibrancy or the DK universal property.
  GraphMappingCategory : PresentedEnrichedCategory (ℓ-suc ℓ) (ℓ-suc ℓ)
  GraphMappingCategory = DKEnrichedCategory {C = RaisedGraphCategory ℓ} RR.graphMarking

  SpaceMappingCategory : PresentedEnrichedCategory (ℓ-suc ℓ) (ℓ-suc ℓ)
  SpaceMappingCategory = DKEnrichedCategory {C = TopCategory ℓ} RR.topMarking

  enrichedComparison : PresentedEnrichedFunctor GraphMappingCategory SpaceMappingCategory
  enrichedComparison = DKEnrichedFunctor
    {C = RaisedGraphCategory ℓ} {D = TopCategory ℓ}
    {R = RR.graphMarking} {S = RR.topMarking} RR.NG-relative

  GraphMappingSpace : Graph ℓ → Graph ℓ → Top (ℓ-suc ℓ)
  GraphMappingSpace G H = M.MappingSpace {C = RaisedGraphCategory ℓ} RR.graphMarking G H

  SpaceMappingSpace : Graph ℓ → Graph ℓ → Top (ℓ-suc ℓ)
  SpaceMappingSpace G H = M.MappingSpace {C = TopCategory ℓ} RR.topMarking (R.NG G) (R.NG H)

  mappingComparison : (G H : Graph ℓ)
                    → Continuous (GraphMappingSpace G H) (SpaceMappingSpace G H)
  mappingComparison G H = M.mappingMap
    {C = RaisedGraphCategory ℓ} {D = TopCategory ℓ}
    {R = RR.graphMarking} {T = RR.topMarking} RR.NG-relative G H

  -- A STATEMENT TYPE, deliberately with no supplied inhabitant.
  -- All dimensions and all graph pairs occur in the second field.
  -- The geometry and localization comparison obligations are separate
  -- foundations, not claimed to follow from type checking this record.
  record DHHStatement : Type (ℓ-suc (ℓ-suc ℓ)) where
    field
      essentially-surjective : O.ObjectDHH
      fully-faithful : (G H : Graph ℓ)
                     → HG-map.WeakHomotopyEquivalence (mappingComparison G H)
  open DHHStatement public

  fullDHH-implies-objectDHH : DHHStatement → O.ObjectDHH
  fullDHH-implies-objectDHH = essentially-surjective
