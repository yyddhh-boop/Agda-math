{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.StableCompositionMergeAssociativity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.CommonStage
open import DHH.Enrichment.GraphHom using (HomGraph)
open import DHH.Enrichment.StableCompositionMergeAssociativityStages public

private variable ℓ : Level

module _ (G H K L : Graph ℓ) where
  private
    A₀ B₀ C₀ D₀ : Graph ℓ
    A₀ = HomGraph K L
    B₀ = HomGraph H K
    C₀ = HomGraph G H
    D₀ = HomGraph G L
    A B C D : CubicalSet ℓ
    A = N∞ A₀
    B = N∞ B₀
    C = N∞ C₀
    D = N∞ D₀
    module AS = CommonStages (Stage A₀) (stageTransition A₀)
    module BS = CommonStages (Stage B₀) (stageTransition B₀)
    module CS = CommonStages (Stage C₀) (stageTransition C₀)

  -- The equality target is a proposition because the output degree is
  -- a set.  Thus no chosen representatives or quotient relation cases
  -- are required.  A finite common stage suffices for every input triple.
  abstract
    actualMergeN∞-associativity : (p q r : ℕ)
      (a : Cell A p) (b : Cell B q) (c : Cell C r)
      → leftActualMerge G H K L p q r a b c
        ≡ rightActualMerge G H K L p q r a b c
    actualMergeN∞-associativity p q r = SQ.elimProp3
      {A = Stable.Tagged A₀ p} {R = Stable.Step A₀ p}
      {B = Stable.Tagged B₀ q} {S = Stable.Step B₀ q}
      {C = Stable.Tagged C₀ r} {T = Stable.Step C₀ r}
      {P = λ a b c → leftActualMerge G H K L p q r a b c
        ≡ rightActualMerge G H K L p q r a b c}
      (λ _ _ _ → snd (cells D ((p + q) + r)) _ _)
      λ { (k , a) (l , b) (m , c) →
        let commonStage = max k (max l m)
            ha : k ≤ commonStage
            ha = left-≤-max {m = k} {n = max l m}
            hb : l ≤ commonStage
            hb = ≤-trans (left-≤-max {m = l} {n = m})
              (right-≤-max {n = max l m} {m = k})
            hc : m ≤ commonStage
            hc = ≤-trans (right-≤-max {n = m} {m = l})
              (right-≤-max {n = max l m} {m = k})
            ea : Stable.point A₀ p (k , a)
              ≡ Stable.point A₀ p (commonStage , AS.advanceCell ha p a)
            ea = AS.point-advance ha p a
            eb : Stable.point B₀ q (l , b)
              ≡ Stable.point B₀ q (commonStage , BS.advanceCell hb q b)
            eb = BS.point-advance hb q b
            ec : Stable.point C₀ r (m , c)
              ≡ Stable.point C₀ r (commonStage , CS.advanceCell hc r c)
            ec = CS.point-advance hc r c
        in cong₃ (leftActualMerge G H K L p q r) ea eb ec
          ∙ actualMergeN∞-associativity-same-stage G H K L commonStage p q r
            (AS.advanceCell ha p a) (BS.advanceCell hb q b) (CS.advanceCell hc r c)
          ∙ sym (cong₃ (rightActualMerge G H K L p q r) ea eb ec) }
