{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.Mapping where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Set

-- A category enriched in simplicial SETS, with a fixed object type.
-- Mapping objects are complete Δ-presheaves, not arbitrarily supplied
-- homotopy types.  This is the target interface for the actual DK
-- degreewise localization of the free-category resolution.
record MappingSimplicialModel {ℓ : Level} (Objects : Type ℓ) (ℓh : Level)
                             : Type (ℓ-max ℓ (ℓ-suc ℓh)) where
  field
    MapΔ : Objects → Objects → SimplicialSet ℓh
    identityΔ : (n : ℕ) (x : Objects) → Simplex (MapΔ x x) n
    composeΔ : {x y z : Objects} (n : ℕ)
             → Simplex (MapΔ x y) n → Simplex (MapΔ y z) n
             → Simplex (MapΔ x z) n
    identity-natural : {m n : ℕ} (u : OrdinalMap m n) (x : Objects)
                     → reindexΔ (MapΔ x x) u (identityΔ n x) ≡ identityΔ m x
    compose-natural : {m n : ℕ} {x y z : Objects} (u : OrdinalMap m n)
                      (f : Simplex (MapΔ x y) n) (g : Simplex (MapΔ y z) n)
                    → reindexΔ (MapΔ x z) u (composeΔ n f g)
                    ≡ composeΔ m (reindexΔ (MapΔ x y) u f) (reindexΔ (MapΔ y z) u g)
    identity-left : {x y : Objects} (n : ℕ) (f : Simplex (MapΔ x y) n)
                  → composeΔ n (identityΔ n x) f ≡ f
    identity-right : {x y : Objects} (n : ℕ) (f : Simplex (MapΔ x y) n)
                   → composeΔ n f (identityΔ n y) ≡ f
    compose-assoc : {w x y z : Objects} (n : ℕ)
                    (f : Simplex (MapΔ w x) n) (g : Simplex (MapΔ x y) n)
                    (h : Simplex (MapΔ y z) n)
                  → composeΔ n (composeΔ n f g) h ≡ composeΔ n f (composeΔ n g h)
open MappingSimplicialModel public
