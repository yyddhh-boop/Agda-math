{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionMergeCore where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.StableNerve.Transitions using (Stage)
open import DHH.StableNerve.Colimit using (N∞; includeStage)
open import DHH.Enrichment.GraphHom using (HomGraph)
open import DHH.Enrichment.StableComposition using (mergeN∞; combineAt)
open import DHH.Enrichment.StableCompositionStageLaws using (mergeN∞-same-stage-abstract)

private variable ℓ : Level

-- The actual checked operation, hidden only from automatic conversion.
-- The equation below identifies it with the original construction.
abstract
  actualMergeN∞ : (G H K : Graph ℓ) (p q : ℕ)
    → Cell (N∞ (HomGraph H K)) p → Cell (N∞ (HomGraph G H)) q
    → Cell (N∞ (HomGraph G K)) (p + q)
  actualMergeN∞ = mergeN∞

  mergeN∞-actual : (G H K : Graph ℓ) (p q : ℕ)
    (a : Cell (N∞ (HomGraph H K)) p) (b : Cell (N∞ (HomGraph G H)) q)
    → mergeN∞ G H K p q a b ≡ actualMergeN∞ G H K p q a b
  mergeN∞-actual G H K p q a b = refl

  actualMergeN∞-same-stage : (G H K : Graph ℓ) (k p q : ℕ)
    (a : Cell (Stage (HomGraph H K) k) p)
    (b : Cell (Stage (HomGraph G H) k) q)
    → actualMergeN∞ G H K p q
        (mapCells {A = Stage (HomGraph H K) k} {B = N∞ (HomGraph H K)}
          (includeStage (HomGraph H K) k) p a)
        (mapCells {A = Stage (HomGraph G H) k} {B = N∞ (HomGraph G H)}
          (includeStage (HomGraph G H) k) q b)
      ≡ mapCells {A = Stage (HomGraph G K) k} {B = N∞ (HomGraph G K)}
          (includeStage (HomGraph G K) k) (p + q) (combineAt G H K k p q a b)
  actualMergeN∞-same-stage G H K k p q a b =
    mergeN∞-same-stage-abstract G H K k p q a b
