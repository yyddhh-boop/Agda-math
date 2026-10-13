{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.PresentationTerminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Categories.Category.Base using (Category)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (here; there; front)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation
open import DHH.Simplicial.PresentationShift

collapseToZero : (m : ℕ) → PresentedMap m zero
collapseToZero m = SQ.[ zeroTargetWord m ]

-- This proof uses the defining simplicial relations, not the concrete
-- semantic uniqueness of a map into [0].  It is a normal-form base case.
face-to-zero : {n : ℕ} (i : Fin (suc (suc n)))
  → SQ.[ faceW i ] ⋆p collapseToZero (suc n) ≡ collapseToZero n
face-to-zero {n = n} fzero =
  sym (Category.⋆Assoc DeltaPresentation SQ.[ faceW fzero ]
    SQ.[ degenW fzero ] (collapseToZero n))
  ∙ cong (_⋆p collapseToZero n) (SQ.eq/ _ _ (same here))
  ∙ Category.⋆IdL DeltaPresentation (collapseToZero n)
face-to-zero {n = n} (fsuc fzero) =
  sym (Category.⋆Assoc DeltaPresentation SQ.[ faceW (fsuc fzero) ]
    SQ.[ degenW fzero ] (collapseToZero n))
  ∙ cong (_⋆p collapseToZero n) (SQ.eq/ _ _ (next here))
  ∙ Category.⋆IdL DeltaPresentation (collapseToZero n)
face-to-zero {n = suc n} (fsuc (fsuc i)) =
  sym (Category.⋆Assoc DeltaPresentation SQ.[ faceW (fsuc (fsuc i)) ]
    SQ.[ degenW fzero ] (collapseToZero (suc n)))
  ∙ cong (_⋆p collapseToZero (suc n))
    (cong (λ j → SQ.[ seqW (faceW (fsuc (fsuc j))) (degenW fzero) ])
      (sym (fin-position-inverse i))
    ∙ SQ.eq/ _ _ (after (front (finPosition i)))
    ∙ cong (λ j → SQ.[ seqW (degenW fzero) (faceW (fsuc j)) ])
      (fin-position-inverse i))
  ∙ Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ]
      SQ.[ faceW (fsuc i) ] (collapseToZero (suc n))
  ∙ cong (SQ.[ degenW fzero ] ⋆p_) (face-to-zero (fsuc i))

degen-to-zero : {n : ℕ} (i : Fin (suc n))
  → SQ.[ degenW i ] ⋆p collapseToZero n ≡ collapseToZero (suc n)
degen-to-zero fzero = refl
degen-to-zero {n = suc n} (fsuc i) =
  sym (Category.⋆Assoc DeltaPresentation SQ.[ degenW (fsuc i) ]
    SQ.[ degenW fzero ] (collapseToZero n))
  ∙ cong (_⋆p collapseToZero n)
    (cong (λ j → SQ.[ seqW (degenW (fsuc j)) (degenW fzero) ])
      (sym (fin-position-inverse i))
    ∙ SQ.eq/ _ _ (symmetric (degens (front (finPosition i))))
    ∙ cong (λ j → SQ.[ seqW (degenW fzero) (degenW j) ])
      (fin-position-inverse i))
  ∙ Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ]
      SQ.[ degenW i ] (collapseToZero n)
  ∙ cong (SQ.[ degenW fzero ] ⋆p_) (degen-to-zero i)

word-to-zero : {m n : ℕ} (w : DeltaWord m n)
  → SQ.[ w ] ⋆p collapseToZero n ≡ collapseToZero m
word-to-zero idW = Category.⋆IdL DeltaPresentation _
word-to-zero (faceW i) = face-to-zero i
word-to-zero (degenW i) = degen-to-zero i
word-to-zero {n = n} (seqW f g) =
  Category.⋆Assoc DeltaPresentation SQ.[ f ] SQ.[ g ] (collapseToZero n)
  ∙ cong (SQ.[ f ] ⋆p_) (word-to-zero g)
  ∙ word-to-zero f

presented-to-zero : {m n : ℕ} (p : PresentedMap m n)
  → p ⋆p collapseToZero n ≡ collapseToZero m
presented-to-zero = SQ.elimProp (λ _ → SQ.squash/ _ _) word-to-zero

zero-target-normalization : {m : ℕ} (p : PresentedMap m zero)
  → p ≡ collapseToZero m
zero-target-normalization p = sym (Category.⋆IdR DeltaPresentation p)
  ∙ presented-to-zero p

zero-target-uniqueness : {m : ℕ} (p q : PresentedMap m zero) → p ≡ q
zero-target-uniqueness p q = zero-target-normalization p ∙ sym (zero-target-normalization q)

zero-target-faithful : {m : ℕ} (p q : PresentedMap m zero)
  → evaluatePresented p ≡ evaluatePresented q → p ≡ q
zero-target-faithful p q _ = zero-target-uniqueness p q
