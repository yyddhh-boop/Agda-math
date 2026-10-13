{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealSimplexLift where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import DHH.Simplicial.Ordinal
open import DHH.Topology.Base
open import DHH.Topology.BasisLift
open import DHH.Realization.Coend
open import DHH.Geometry.RealSimplex

-- Lift the small basis of the actual ordered-coordinate simplex.
-- The same real geometry is used at the mapping-space universe.
module RealSimplexLifting (ℓ : Level) where
  liftedRealSimplex : ℕ → Top (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  liftedRealSimplex n = BasisLifting.liftedTop ℓ (simplexBasis n)
    (carrier-isSet (RealSimplex n))

  liftedSimplexMap : {m n : ℕ} → OrdinalMap m n
    → Continuous (liftedRealSimplex m) (liftedRealSimplex n)
  liftedSimplexMap {m} {n} f = liftBasisContinuous ℓ
    (simplexBasis m) (simplexBasis n)
    (carrier-isSet (RealSimplex m)) (carrier-isSet (RealSimplex n))
    (simplexMap f)

  liftedSimplexMap-id : (n : ℕ)
    → liftedSimplexMap (ordinalId n) ≡ identityContinuous (liftedRealSimplex n)
  liftedSimplexMap-id n = continuousExt λ x →
    cong lift (cong (λ h → carrierMap h (lower x)) (simplexMap-id n))

  liftedSimplexMap-compose : {l m n : ℕ} (f : OrdinalMap l m) (g : OrdinalMap m n)
    → liftedSimplexMap (f ⋆o g)
      ≡ composeContinuous (liftedSimplexMap g) (liftedSimplexMap f)
  liftedSimplexMap-compose f g = continuousExt λ x →
    cong lift (cong (λ h → carrierMap h (lower x)) (simplexMap-compose f g))

  liftedRealSimplexDiagram : DiskDiagram Delta (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  disk liftedRealSimplexDiagram = liftedRealSimplex
  diskMap liftedRealSimplexDiagram = liftedSimplexMap
  disk-id liftedRealSimplexDiagram {a = n} = liftedSimplexMap-id n
  disk-compose liftedRealSimplexDiagram = liftedSimplexMap-compose

standardMappingSimplexDiagram : DiskDiagram Delta (ℓ-suc (ℓ-suc ℓ-zero))
standardMappingSimplexDiagram = RealSimplexLifting.liftedRealSimplexDiagram
  (ℓ-suc (ℓ-suc ℓ-zero))
