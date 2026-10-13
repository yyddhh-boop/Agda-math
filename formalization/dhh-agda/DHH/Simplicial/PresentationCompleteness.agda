{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.PresentationCompleteness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_; isEquiv)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (fst; snd)
open import Cubical.Categories.Functor.Base
import Cubical.HITs.SetQuotients as SQ
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation
open import DHH.Simplicial.NormalForm
open import DHH.Simplicial.WordNormalization

-- This theorem closes the gap between concrete semantic equality and
-- the ORIGINAL generators-and-relations quotient.  No new relation or
-- normal-form correctness axiom is added to the quotient definition.
normalization-evaluation : {m n : ℕ} (w : DeltaWord m n)
  → normalSemantics (normalizeWord w) ≡ evalWord w
normalization-evaluation w = sym (normal-word-evaluation (normalizeWord w))
  ∙ sym (cong evaluatePresented (word-normalization w))

word-evaluation-faithful : {m n : ℕ} (f g : DeltaWord m n)
  → evalWord f ≡ evalWord g → SQ.[ f ] ≡ SQ.[ g ]
word-evaluation-faithful f g e = word-normalization f
  ∙ cong (λ q → SQ.[ normalWord q ])
      (normal-semantic-injective (normalizeWord f) (normalizeWord g)
        (normalization-evaluation f ∙ e ∙ sym (normalization-evaluation g)))
  ∙ sym (word-normalization g)

presentation-faithful : {m n : ℕ} (p q : PresentedMap m n)
  → evaluatePresented p ≡ evaluatePresented q → p ≡ q
presentation-faithful = SQ.elimProp2
  (λ p q → isPropΠ (λ _ → SQ.squash/ p q)) word-evaluation-faithful

inversePresentationMap : {m n : ℕ} → OrdinalMap m n → PresentedMap m n
inversePresentationMap f = SQ.[ fst (normalizeOrdinal f) ]

inversePresentation-section : {m n : ℕ} (f : OrdinalMap m n)
  → evaluatePresented (inversePresentationMap f) ≡ f
inversePresentation-section f = snd (normalizeOrdinal f)

inversePresentation-retraction : {m n : ℕ} (p : PresentedMap m n)
  → inversePresentationMap (evaluatePresented p) ≡ p
inversePresentation-retraction p = presentation-faithful _ _
  (inversePresentation-section (evaluatePresented p))

presentationHomIso : {m n : ℕ} → Iso (PresentedMap m n) (OrdinalMap m n)
Iso.fun presentationHomIso = evaluatePresented
Iso.inv presentationHomIso = inversePresentationMap
Iso.rightInv presentationHomIso = inversePresentation-section
Iso.leftInv presentationHomIso = inversePresentation-retraction

presentationHomEquivalence : {m n : ℕ} → PresentedMap m n ≃ OrdinalMap m n
presentationHomEquivalence = isoToEquiv presentationHomIso

presentation-isEquiv : {m n : ℕ} → isEquiv (evaluatePresented {m = m} {n = n})
presentation-isEquiv = snd presentationHomEquivalence

-- Since objects are literally the same natural numbers, full faithful
-- hom equivalences lift to mutually inverse functors without object
-- choices or essential-surjectivity witnesses.
presentationInverse : Functor Delta DeltaPresentation
Functor.F-ob presentationInverse n = n
Functor.F-hom presentationInverse = inversePresentationMap
Functor.F-id presentationInverse = presentation-faithful _ _
  (inversePresentation-section (ordinalId _))
Functor.F-seq presentationInverse f g = presentation-faithful _ _
  (inversePresentation-section (f ⋆o g)
  ∙ sym (evaluation-compose (inversePresentationMap f) (inversePresentationMap g)
      ∙ cong₂ _⋆o_ (inversePresentation-section f) (inversePresentation-section g)))

evaluation-after-inverse : funcComp presentationEvaluation presentationInverse ≡ Id
evaluation-after-inverse = Functor≡ (λ _ → refl) inversePresentation-section

inverse-after-evaluation : funcComp presentationInverse presentationEvaluation ≡ Id
inverse-after-evaluation = Functor≡ (λ _ → refl) inversePresentation-retraction
