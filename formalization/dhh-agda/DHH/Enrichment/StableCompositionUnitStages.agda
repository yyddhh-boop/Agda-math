{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionUnitStages where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Sigma
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayUnitLift
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.StableComposition
open import DHH.Enrichment.StableCompositionIdentity
open import DHH.Enrichment.StableCompositionMergeCore
open import DHH.Enrichment.GridCompositionCoherence

private variable ℓ : Level

abstract
  leftIdentity-sync : (G H : Graph ℓ) (k p q : ℕ)
    (v : Cell (DayUnitAt ℓ) p) (b : Cell (Stage (HomGraph G H) k) q)
    → actualMergeN∞ G H H p q (mapCells (stableIdentity H) p v)
        (mapCells (includeStage (HomGraph G H) k) q b)
      ≡ actualMergeN∞ G H H p q
        (mapCells (includeStage (HomGraph H H) k) p
          (constantHom {G = Grid (suc k) p} (HomGraph H H) (idHom H)))
        (mapCells (includeStage (HomGraph G H) k) q b)
  leftIdentity-sync G H k p q v b = congS
    {A = Cell (N∞ (HomGraph H H)) p} {B = Cell (N∞ (HomGraph G H)) (p + q)}
    (λ a → actualMergeN∞ G H H p q a (mapCells (includeStage (HomGraph G H) k) q b))
    (stableIdentity-at-stage H k p v)

abstract
  leftIdentity-merge-stage : (G H : Graph ℓ) (k p q : ℕ)
    (b : Cell (Stage (HomGraph G H) k) q)
    → actualMergeN∞ G H H p q
        (mapCells (includeStage (HomGraph H H) k) p
          (constantHom {G = Grid (suc k) p} (HomGraph H H) (idHom H)))
        (mapCells (includeStage (HomGraph G H) k) q b)
      ≡ mapCells (includeStage (HomGraph G H) k) (p + q)
        (combineAt G H H k p q
          (constantHom {G = Grid (suc k) p} (HomGraph H H) (idHom H)) b)
  leftIdentity-merge-stage G H k p q b = actualMergeN∞-same-stage G H H k p q
    (constantHom {G = Grid (suc k) p} (HomGraph H H) (idHom H)) b

abstract
  leftIdentity-grid-stage : (G H : Graph ℓ) (k p q : ℕ)
    (v : Cell (DayUnitAt ℓ) p) (b : Cell (Stage (HomGraph G H) k) q)
    → combineAt G H H k p q
        (constantHom {G = Grid (suc k) p} (HomGraph H H) (idHom H)) b
      ≡ reindex (Stage (HomGraph G H) k) (lower v ⊗c cubeId q) b
  leftIdentity-grid-stage G H k p q v b =
    composeGrid-left-unit (suc k) p q {G = G} {H = H} (lower v) b

abstract
  leftIdentity-stable-stage : (G H : Graph ℓ) (k p q : ℕ)
    (v : Cell (DayUnitAt ℓ) p) (b : Cell (Stage (HomGraph G H) k) q)
    → actualMergeN∞ G H H p q (mapCells (stableIdentity H) p v)
        (mapCells (includeStage (HomGraph G H) k) q b)
      ≡ reindex (N∞ (HomGraph G H)) (lower v ⊗c cubeId q)
        (mapCells (includeStage (HomGraph G H) k) q b)
  leftIdentity-stable-stage G H k p q v b =
    leftIdentity-sync G H k p q v b
    ∙ leftIdentity-merge-stage G H k p q b
    ∙ cong (mapCells {A = Stage (HomGraph G H) k} {B = N∞ (HomGraph G H)}
        (includeStage (HomGraph G H) k) (p + q))
        (leftIdentity-grid-stage G H k p q v b)
    ∙ natural {A = Stage (HomGraph G H) k} {B = N∞ (HomGraph G H)}
        (includeStage (HomGraph G H) k) (lower v ⊗c cubeId q) b

abstract
  rightIdentity-sync : (G H : Graph ℓ) (k p q : ℕ)
    (a : Cell (Stage (HomGraph G H) k) p) (v : Cell (DayUnitAt ℓ) q)
    → actualMergeN∞ G G H p q
        (mapCells (includeStage (HomGraph G H) k) p a)
        (mapCells (stableIdentity G) q v)
      ≡ actualMergeN∞ G G H p q
        (mapCells (includeStage (HomGraph G H) k) p a)
        (mapCells (includeStage (HomGraph G G) k) q
          (constantHom {G = Grid (suc k) q} (HomGraph G G) (idHom G)))
  rightIdentity-sync G H k p q a v = congS
    {A = Cell (N∞ (HomGraph G G)) q} {B = Cell (N∞ (HomGraph G H)) (p + q)}
    (actualMergeN∞ G G H p q (mapCells (includeStage (HomGraph G H) k) p a))
    (stableIdentity-at-stage G k q v)

abstract
  rightIdentity-merge-stage : (G H : Graph ℓ) (k p q : ℕ)
    (a : Cell (Stage (HomGraph G H) k) p)
    → actualMergeN∞ G G H p q
        (mapCells (includeStage (HomGraph G H) k) p a)
        (mapCells (includeStage (HomGraph G G) k) q
          (constantHom {G = Grid (suc k) q} (HomGraph G G) (idHom G)))
      ≡ mapCells (includeStage (HomGraph G H) k) (p + q)
        (combineAt G G H k p q a
          (constantHom {G = Grid (suc k) q} (HomGraph G G) (idHom G)))
  rightIdentity-merge-stage G H k p q a = actualMergeN∞-same-stage G G H k p q a
    (constantHom {G = Grid (suc k) q} (HomGraph G G) (idHom G))

abstract
  rightIdentity-grid-stage : (G H : Graph ℓ) (k p q : ℕ)
    (a : Cell (Stage (HomGraph G H) k) p) (v : Cell (DayUnitAt ℓ) q)
    → combineAt G G H k p q a
        (constantHom {G = Grid (suc k) q} (HomGraph G G) (idHom G))
      ≡ reindex (Stage (HomGraph G H) k)
        ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a
  rightIdentity-grid-stage G H k p q a v =
    composeGrid-right-unit (suc k) p q {G = G} {H = H} (lower v) a

abstract
  rightIdentity-stable-stage : (G H : Graph ℓ) (k p q : ℕ)
    (a : Cell (Stage (HomGraph G H) k) p) (v : Cell (DayUnitAt ℓ) q)
    → actualMergeN∞ G G H p q
        (mapCells (includeStage (HomGraph G H) k) p a)
        (mapCells (stableIdentity G) q v)
      ≡ reindex (N∞ (HomGraph G H)) ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p)
        (mapCells (includeStage (HomGraph G H) k) p a)
  rightIdentity-stable-stage G H k p q a v =
    rightIdentity-sync G H k p q a v
    ∙ rightIdentity-merge-stage G H k p q a
    ∙ cong (mapCells {A = Stage (HomGraph G H) k} {B = N∞ (HomGraph G H)}
        (includeStage (HomGraph G H) k) (p + q))
        (rightIdentity-grid-stage G H k p q a v)
    ∙ natural {A = Stage (HomGraph G H) k} {B = N∞ (HomGraph G H)}
        (includeStage (HomGraph G H) k) ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a
