{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionStageLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.StableNerve.Transitions using (Stage)
open import DHH.StableNerve.Colimit using (N∞; includeStage)
open import DHH.Enrichment.GraphHom using (HomGraph)
open import DHH.Enrichment.StableComposition using (mergeN∞; combineAt; mergeN∞-same-stage)

private variable ℓ : Level

-- Exact abstract copy of the verified same-stage law. The map and its
-- mathematical statement are unchanged; clients need only its path
-- type, and do not need to normalize its large quotient proof body.
abstract
  mergeN∞-same-stage-abstract : (G H K : Graph ℓ) (k p q : ℕ)
    (a : Cell (Stage (HomGraph H K) k) p)
    (b : Cell (Stage (HomGraph G H) k) q)
    → mergeN∞ G H K p q
        (mapCells {A = Stage (HomGraph H K) k} {B = N∞ (HomGraph H K)}
          (includeStage (HomGraph H K) k) p a)
        (mapCells {A = Stage (HomGraph G H) k} {B = N∞ (HomGraph G H)}
          (includeStage (HomGraph G H) k) q b)
      ≡ mapCells {A = Stage (HomGraph G K) k} {B = N∞ (HomGraph G K)}
          (includeStage (HomGraph G K) k) (p + q) (combineAt G H K k p q a b)
  mergeN∞-same-stage-abstract G H K k p q a b =
    mergeN∞-same-stage G H K k p q a b
