{-# OPTIONS --cubical --safe #-}

module DHH.Realization.Examples where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.Cubes using (PointGraph; Q; Cube; here)
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.Coend
open import DHH.Realization.Graph

deleteAll : (n : ℕ) → CubicalMap n 0
deleteAll zero = cubeId zero
deleteAll (suc n) = cubeDelete here ⋆c deleteAll n

-- A genuine ALL-DIMENSIONAL check of the coend identifications: the
-- nerve of a one-point graph realizes to a one-point carrier, for any
-- supplied geometry whose zero disk is a point.  This does not assert
-- anything about arbitrary graphs or identify toy disks with real ones.
module _ (E : CubeGeometry ℓ-zero) where
  module GR = GraphRealization E
  module R = GR.R PointGraph

  pointCube : Cube PointGraph 0
  pointCube = idHom PointGraph

  centre : Carrier (GR.NG PointGraph)
  centre = R.point 0 pointCube (zeroPoint E)

  all-pieces-at-centre : (p : R.Pieces) → SQ.[ p ] ≡ centre
  all-pieces-at-centre (n , c , t) =
    cong (λ k → R.point n k t) (homExt (λ _ → refl))
    ∙ R.face-identification (deleteAll n) pointCube t
    ∙ cong (R.point 0 pointCube)
        (zero-contractible E (carrierMap (diskMap (diagram E) (deleteAll n)) t))

  point-realization-contractible : isContr (Carrier (GR.NG PointGraph))
  point-realization-contractible = centre ,
    SQ.elimProp (λ p → carrier-isSet (GR.NG PointGraph) centre p)
      (λ p → sym (all-pieces-at-centre p))
