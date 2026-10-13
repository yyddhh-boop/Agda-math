{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealCubeChecks where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (isPropUnit*)
open import Cubical.Categories.Category.Base using (CatIso; isIso)
open import DHH.Cubes using (Position; here)
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Topology.Category
open import DHH.Geometry.DedekindReals
open import DHH.Geometry.IntervalLattice
open import DHH.Geometry.RealTopology
open import DHH.Geometry.RealCubes
open import DHH.Geometry.RealCubeDiagram

-- The semantic descent retains each standard generator computation.
realCubeAction-face : {n : ℕ} (p : Position (suc n)) (b : Bool)
  → realCubeAction (cubeFace p b) ≡ CubePowers.insertMap p (endpoint b)
realCubeAction-face p b = refl

realCubeAction-delete : {n : ℕ} (p : Position (suc n))
  → realCubeAction (cubeDelete p) ≡ CubePowers.deleteMap p
realCubeAction-delete p = refl

realCubeAction-min : {n : ℕ} (p : Position (suc n))
  → realCubeAction (cubeMin p) ≡ CubePowers.mergeMap p intervalMinContinuous
realCubeAction-min p = refl

realCubeAction-max : {n : ℕ} (p : Position (suc n))
  → realCubeAction (cubeMax p) ≡ CubePowers.mergeMap p intervalMaxContinuous
realCubeAction-max p = refl

cubeOneToInterval : Continuous (RealCube 1) closedUnitInterval
cubeOneToInterval = CubePowers.headMap 0

intervalToCubeOne : Continuous closedUnitInterval (RealCube 1)
intervalToCubeOne = CubePowers.consMaps 0 (identityContinuous closedUnitInterval)
  (constantContinuous closedUnitInterval (RealCube 0) realCubeZero)

-- An actual homeomorphism, expressed as an isomorphism in Top, not
-- just a bijection of carriers or a homotopy equivalence.
cubeOneIntervalHomeomorphism :
  CatIso (TopCategory (ℓ-suc ℓ-zero)) (RealCube 1) closedUnitInterval
fst cubeOneIntervalHomeomorphism = cubeOneToInterval
isIso.inv (snd cubeOneIntervalHomeomorphism) = intervalToCubeOne
isIso.sec (snd cubeOneIntervalHomeomorphism) = continuousExt (λ _ → refl)
isIso.ret (snd cubeOneIntervalHomeomorphism) = continuousExt λ { (x , u) i →
  x , isPropUnit* realCubeZero u i }

cubeOne-endpoint : (b : Bool)
  → carrierMap cubeOneToInterval
      (carrierMap (realCubeAction (cubeFace here b)) realCubeZero) ≡ endpoint b
cubeOne-endpoint b = refl

cubeOne-endpoints-distinct :
  carrierMap (realCubeAction (cubeFace here false)) realCubeZero
  ≡ carrierMap (realCubeAction (cubeFace here true)) realCubeZero → ⊥
cubeOne-endpoints-distinct p = intervalZero≠intervalOne
  (cong (carrierMap cubeOneToInterval) p)
