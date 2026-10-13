{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionMergeAssociativityStages where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCoherence using (cubeAssociator)
open import DHH.StableNerve.Transitions using (Stage)
open import DHH.StableNerve.Colimit using (N∞; includeStage)
open import DHH.Enrichment.GraphHom using (HomGraph)
open import DHH.Enrichment.StableComposition using (combineAt)
open import DHH.Enrichment.StableCompositionMergeCore
open import DHH.Enrichment.GridCompositionCoherence using (composeGrid-associativity)

private variable ℓ : Level

-- All higher quotient proofs use the checked opaque operation.  No new
-- composition, and no new relation on stable cells, is introduced here.
module _ (G H K L : Graph ℓ) where
  private
    A₀ B₀ C₀ D₀ N₀ M₀ : Graph ℓ
    A₀ = HomGraph K L
    B₀ = HomGraph H K
    C₀ = HomGraph G H
    D₀ = HomGraph G L
    N₀ = HomGraph H L
    M₀ = HomGraph G K
    A B C D N M : CubicalSet ℓ
    A = N∞ A₀
    B = N∞ B₀
    C = N∞ C₀
    D = N∞ D₀
    N = N∞ N₀
    M = N∞ M₀

  leftActualMerge : (p q r : ℕ)
    → Cell A p → Cell B q → Cell C r → Cell D ((p + q) + r)
  leftActualMerge p q r a b c =
    actualMergeN∞ G H L (p + q) r (actualMergeN∞ H K L p q a b) c

  rightActualMerge : (p q r : ℕ)
    → Cell A p → Cell B q → Cell C r → Cell D ((p + q) + r)
  rightActualMerge p q r a b c = reindex D (cubeAssociator p q r)
    (actualMergeN∞ G K L p (q + r) a (actualMergeN∞ G H K q r b c))

  abstract
    leftActualMerge-stage : (k p q r : ℕ)
      (a : Cell (Stage A₀ k) p)
      (b : Cell (Stage B₀ k) q)
      (c : Cell (Stage C₀ k) r)
      → leftActualMerge p q r
          (mapCells (includeStage A₀ k) p a)
          (mapCells (includeStage B₀ k) q b)
          (mapCells (includeStage C₀ k) r c)
        ≡ mapCells (includeStage D₀ k) ((p + q) + r)
          (combineAt G H L k (p + q) r (combineAt H K L k p q a b) c)
    leftActualMerge-stage k p q r a b c =
      congS {A = Cell N (p + q)} {B = Cell D ((p + q) + r)}
        (λ ab → actualMergeN∞ G H L (p + q) r ab
          (mapCells (includeStage C₀ k) r c))
        (actualMergeN∞-same-stage H K L k p q a b)
      ∙ actualMergeN∞-same-stage G H L k (p + q) r
        (combineAt H K L k p q a b) c

  abstract
    rightActualMerge-stage : (k p q r : ℕ)
      (a : Cell (Stage A₀ k) p)
      (b : Cell (Stage B₀ k) q)
      (c : Cell (Stage C₀ k) r)
      → rightActualMerge p q r
          (mapCells (includeStage A₀ k) p a)
          (mapCells (includeStage B₀ k) q b)
          (mapCells (includeStage C₀ k) r c)
        ≡ reindex D (cubeAssociator p q r)
          (mapCells (includeStage D₀ k) (p + (q + r))
            (combineAt G K L k p (q + r) a (combineAt G H K k q r b c)))
    rightActualMerge-stage k p q r a b c =
      congS {A = Cell D (p + (q + r))} {B = Cell D ((p + q) + r)}
        (reindex D (cubeAssociator p q r))
        (congS {A = Cell M (q + r)} {B = Cell D (p + (q + r))}
          (actualMergeN∞ G K L p (q + r) (mapCells (includeStage A₀ k) p a))
          (actualMergeN∞-same-stage G H K k q r b c)
        ∙ actualMergeN∞-same-stage G K L k p (q + r) a
          (combineAt G H K k q r b c))

  abstract
    actualMergeN∞-associativity-same-stage : (k p q r : ℕ)
      (a : Cell (Stage A₀ k) p)
      (b : Cell (Stage B₀ k) q)
      (c : Cell (Stage C₀ k) r)
      → leftActualMerge p q r
          (mapCells (includeStage A₀ k) p a)
          (mapCells (includeStage B₀ k) q b)
          (mapCells (includeStage C₀ k) r c)
        ≡ rightActualMerge p q r
          (mapCells (includeStage A₀ k) p a)
          (mapCells (includeStage B₀ k) q b)
          (mapCells (includeStage C₀ k) r c)
    actualMergeN∞-associativity-same-stage k p q r a b c =
      leftActualMerge-stage k p q r a b c
      ∙ congS {A = Cell (Stage D₀ k) ((p + q) + r)}
          {B = Cell D ((p + q) + r)}
          (mapCells (includeStage D₀ k) ((p + q) + r))
          (composeGrid-associativity (suc k) p q r
            {G = G} {H = H} {K = K} {L = L} a b c)
      ∙ natural {A = Stage D₀ k} {B = D}
          (includeStage D₀ k) (cubeAssociator p q r)
          (combineAt G K L k p (q + r) a (combineAt G H K k q r b c))
      ∙ sym (rightActualMerge-stage k p q r a b c)
