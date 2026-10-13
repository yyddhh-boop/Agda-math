{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealCubeLift where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Topology.BasisLift
open import DHH.Topology.FinitePowers using (powerBasis; power-isSet)
open import DHH.Topology.WeakEquivalence using (CubeGeometry; diagram; zeroPoint; zero-contractible)
open import DHH.Realization.Coend using (DiskDiagram; disk; diskMap; disk-id; disk-compose)
open import DHH.Geometry.DedekindReals
open import DHH.Geometry.RealTopology
open import DHH.Geometry.RealCubes
open import DHH.Geometry.RealCubeDiagram

-- The larger-universe model is the basis lift of the SAME actual real
-- cubes and continuous maps.  It does not resize arbitrary predicates.
module RealCubeLifting (ℓ : Level) where
  liftedRealCube : ℕ → Top (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  liftedRealCube n = BasisLifting.liftedTop ℓ (powerBasis intervalBasis n)
    (power-isSet isSetClosedUnitInterval n)

  liftedRealCubeAction : {m n : ℕ} → CubicalMap m n
    → Continuous (liftedRealCube m) (liftedRealCube n)
  liftedRealCubeAction {m} {n} u = liftBasisContinuous ℓ
    (powerBasis intervalBasis m) (powerBasis intervalBasis n)
    (power-isSet isSetClosedUnitInterval m) (power-isSet isSetClosedUnitInterval n)
    (realCubeAction u)

  liftedRealCubeAction-computes : {m n : ℕ} (u : CubicalMap m n) (x : Carrier (RealCube m))
    → carrierMap (liftedRealCubeAction u) (lift x) ≡ lift (carrierMap (realCubeAction u) x)
  liftedRealCubeAction-computes u x = refl

  liftedRealCubeAction-id : (n : ℕ)
    → liftedRealCubeAction (cubeId n) ≡ identityContinuous (liftedRealCube n)
  liftedRealCubeAction-id n = continuousExt (λ _ → refl)

  liftedRealCubeAction-compose : {m n k : ℕ} (f : CubicalMap m n) (g : CubicalMap n k)
    → liftedRealCubeAction (f ⋆c g)
      ≡ composeContinuous (liftedRealCubeAction g) (liftedRealCubeAction f)
  liftedRealCubeAction-compose f g = continuousExt λ x →
    cong lift (cong (λ h → carrierMap h (lower x)) (realCubeAction-compose f g))

  liftedStandardCubeDiagram : DiskDiagram CubeCategory (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  disk liftedStandardCubeDiagram = liftedRealCube
  diskMap liftedStandardCubeDiagram = liftedRealCubeAction
  disk-id liftedStandardCubeDiagram {a = n} = liftedRealCubeAction-id n
  disk-compose liftedStandardCubeDiagram = liftedRealCubeAction-compose

  liftedStandardCubeGeometry : CubeGeometry (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  diagram liftedStandardCubeGeometry = liftedStandardCubeDiagram
  zeroPoint liftedStandardCubeGeometry = lift realCubeZero
  zero-contractible liftedStandardCubeGeometry x = cong lift (realCubeZero-singleton (lower x))

-- The mapping spaces of the Type₁ graph category inhabit Type₂.
standardMappingCubeGeometry : CubeGeometry (ℓ-suc (ℓ-suc ℓ-zero))
standardMappingCubeGeometry = RealCubeLifting.liftedStandardCubeGeometry (ℓ-suc (ℓ-suc ℓ-zero))
