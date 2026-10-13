{-# OPTIONS --cubical --safe #-}

module DHH.Realization.GeometryBoundaryCheck where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (false; true)
open import Cubical.Data.Sigma
open import DHH.Graph using (Vertex; vertex-isSet)
open import DHH.Cubes using (Q)
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.DiscreteCubes

module Bad = HomotopyGroups DiscreteCubeGeometry

-- A checked semantic boundary: the test geometry connects ANY two
-- points of ANY space.  Therefore possessing CubeGeometry alone cannot
-- identify the ordinary homotopy theory or the original DHH.
discrete-test-connects-any-points : (X : Top ℓ-zero) (x y : Carrier X)
                                → Bad.TopologicalPath X x y
Bad.pathMap (discrete-test-connects-any-points X x y) =
  fromDiscrete (Vertex (Q 1) , vertex-isSet (Q 1)) X labels
  where
  labels : Vertex (Q 1) → Carrier X
  labels (false , _) = x
  labels (true , _) = y
Bad.start (discrete-test-connects-any-points X x y) = refl
Bad.end (discrete-test-connects-any-points X x y) = refl
