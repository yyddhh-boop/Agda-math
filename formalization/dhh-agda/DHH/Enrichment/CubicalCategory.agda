{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.CubicalCategory where

open import Cubical.Foundations.Prelude
open import DHH.CubicalNerve
open import DHH.Cubical.Kan using (IsKan)
open import DHH.Cubical.DayTensor using (DayTensor)
open import DHH.Cubical.DayTensorFunctor using (dayMap)
open import DHH.Cubical.DayUnitLift using (DayUnitAt; dayLeftUnitAt; dayRightUnitAt)
open import DHH.Cubical.DayAssociator using (dayAssociator)

-- A category enriched in this repository's concrete Day monoidal
-- category of cubical SET-valued presheaves.  The object type is arbitrary:
-- no set-truncation hypothesis on objects is imposed.
-- This data is not itself a simplicial category or a simplicial nerve.
record CubicalCategory (ℓO ℓH : Level) : Type (ℓ-suc (ℓ-max ℓO ℓH)) where
  field
    Obj : Type ℓO
    Hom : Obj → Obj → CubicalSet ℓH
    unit : (x : Obj) → CubicalNatural (DayUnitAt ℓH) (Hom x x)
    compose : (x y z : Obj)
      → CubicalNatural (DayTensor (Hom y z) (Hom x y)) (Hom x z)

    compose-left-unit : (x y : Obj)
      → dayMap {A = DayUnitAt ℓH} {A' = Hom y y} {B = Hom x y} {B' = Hom x y}
          (unit y) (cubicalId (Hom x y)) ⋆n compose x y y
        ≡ dayLeftUnitAt (Hom x y)

    compose-right-unit : (x y : Obj)
      → dayMap {A = Hom x y} {A' = Hom x y} {B = DayUnitAt ℓH} {B' = Hom x x}
          (cubicalId (Hom x y)) (unit x) ⋆n compose x x y
        ≡ dayRightUnitAt (Hom x y)

    compose-associativity : (w x y z : Obj)
      → dayMap {A = DayTensor (Hom y z) (Hom x y)} {A' = Hom x z}
          {B = Hom w x} {B' = Hom w x}
          (compose x y z) (cubicalId (Hom w x)) ⋆n compose w x z
        ≡ dayAssociator (Hom y z) (Hom x y) (Hom w x)
          ⋆n (dayMap {A = Hom y z} {A' = Hom y z}
              {B = DayTensor (Hom x y) (Hom w x)} {B' = Hom w y}
              (cubicalId (Hom y z)) (compose w x y) ⋆n compose w y z)
open CubicalCategory public

-- Local fibrancy concerns every hom cubical set.  It retains the checked
-- truncated-existence IsKan property, not a chosen filler algorithm.
LocallyKan : {ℓO ℓH : Level} → CubicalCategory ℓO ℓH → Type (ℓ-max ℓO ℓH)
LocallyKan C = (x y : Obj C) → IsKan (Hom C x y)
