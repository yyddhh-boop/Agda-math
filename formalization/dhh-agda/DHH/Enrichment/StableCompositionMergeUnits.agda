{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionMergeUnits where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociatorHelpers using (dayTensorExt)
open import DHH.Cubical.DayTriple
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayUnitLift
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.CommonStage
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.StableComposition
open import DHH.Enrichment.StableCompositionMergeCore
open import DHH.Enrichment.StableCompositionUnitStages
open import DHH.Enrichment.GridCompositionCoherence

open import DHH.Enrichment.StableCompositionIdentity

private variable ℓ : Level

module _ (G H : Graph ℓ) where
  private
    A : CubicalSet ℓ
    A = N∞ (HomGraph G H)
    U : CubicalSet ℓ
    U = DayUnitAt ℓ
    HH : CubicalSet ℓ
    HH = N∞ (HomGraph H H)
    GG : CubicalSet ℓ
    GG = N∞ (HomGraph G G)

  abstract
    actualMergeN∞-left-unit : (p q : ℕ) (v : Cell (DayUnitAt ℓ) p) (b : Cell A q)
      → actualMergeN∞ G H H p q (mapCells (stableIdentity H) p v) b
        ≡ reindex A (lower v ⊗c cubeId q) b
    actualMergeN∞-left-unit p q v = SQ.elimProp
      {A = Stable.Tagged (HomGraph G H) q} {R = Stable.Step (HomGraph G H) q}
      {P = λ b → actualMergeN∞ G H H p q (mapCells (stableIdentity H) p v) b
        ≡ reindex A (lower v ⊗c cubeId q) b}
      (λ _ → snd (cells A (p + q)) _ _)
      (λ { (k , b) → leftIdentity-stable-stage G H k p q v b })

    actualMergeN∞-right-unit : (p q : ℕ) (a : Cell A p) (v : Cell (DayUnitAt ℓ) q)
      → actualMergeN∞ G G H p q a (mapCells (stableIdentity G) q v)
        ≡ reindex A ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a
    actualMergeN∞-right-unit p q a v = SQ.elimProp
      {A = Stable.Tagged (HomGraph G H) p} {R = Stable.Step (HomGraph G H) p}
      {P = λ a → actualMergeN∞ G G H p q a (mapCells (stableIdentity G) q v)
        ≡ reindex A ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a}
      (λ _ → snd (cells A (p + q)) _ _)
      (λ { (k , a) → rightIdentity-stable-stage G H k p q a v }) a


  -- Recover the laws for the original public operation by its checked
  -- application equation; no replacement composition is asserted.
  abstract
    mergeN∞-left-unit : (p q : ℕ) (v : Cell (DayUnitAt ℓ) p) (b : Cell A q)
      → mergeN∞ G H H p q (mapCells (stableIdentity H) p v) b
        ≡ reindex A (lower v ⊗c cubeId q) b
    mergeN∞-left-unit p q v b =
      mergeN∞-actual G H H p q (mapCells (stableIdentity H) p v) b
      ∙ actualMergeN∞-left-unit p q v b

    mergeN∞-right-unit : (p q : ℕ) (a : Cell A p) (v : Cell (DayUnitAt ℓ) q)
      → mergeN∞ G G H p q a (mapCells (stableIdentity G) q v)
        ≡ reindex A ((cubeId p ⊗c lower v) ⋆c cubeRightUnit p) a
    mergeN∞-right-unit p q a v =
      mergeN∞-actual G G H p q a (mapCells (stableIdentity G) q v)
      ∙ actualMergeN∞-right-unit p q a v
