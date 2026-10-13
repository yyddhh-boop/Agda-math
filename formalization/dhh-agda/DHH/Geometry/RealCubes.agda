{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealCubes where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (tt*; isPropUnit*)
open import DHH.CubeCategory using (CubeWord; identityW; faceW; deleteW; minW; maxW; composeW)
open import DHH.Topology.Base
open import DHH.Topology.FinitePowers
open import DHH.Geometry.DedekindReals
open import DHH.Geometry.RealTopology

-- Actual [0,1]^n with the finite product of rational-interval subspace
-- topologies.  These are not finite vertex sets and not an input record.
module CubePowers = FinitePowers intervalBasis isSetClosedUnitInterval

RealCube : ℕ → Top (ℓ-suc ℓ-zero)
RealCube = CubePowers.powerTop

endpoint : Bool → ClosedUnitInterval
endpoint false = intervalZero
endpoint true = intervalOne

realCubeWord : {m n : ℕ} → CubeWord m n → Continuous (RealCube m) (RealCube n)
realCubeWord identityW = identityContinuous _
realCubeWord (faceW p b) = CubePowers.insertMap p (endpoint b)
realCubeWord (deleteW p) = CubePowers.deleteMap p
realCubeWord (minW p) = CubePowers.mergeMap p intervalMinContinuous
realCubeWord (maxW p) = CubePowers.mergeMap p intervalMaxContinuous
realCubeWord (composeW f g) = composeContinuous (realCubeWord g) (realCubeWord f)

realCubeZero : Carrier (RealCube 0)
realCubeZero = tt*

realCubeZero-singleton : (x : Carrier (RealCube 0)) → x ≡ realCubeZero
realCubeZero-singleton x = isPropUnit* x realCubeZero

-- A DiskDiagram on the concrete CubeCategory additionally needs:
-- Boolean-equal generator words have equal realCubeWord maps.
-- This descent is a theorem to prove, not an extra geometry assumption.
