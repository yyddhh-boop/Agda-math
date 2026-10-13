{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.Presentation where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (Position; weakenPosition; there;
  CoordinatePair; lower; upper; lowerWide; upperWide)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.OrdinalLaws
open import DHH.Simplicial.Word

faceWord : {n : ℕ} → Position (suc (suc n)) → DeltaWord n (suc n)
faceWord i = faceW (positionFin i)

degenWord : {n : ℕ} → Position (suc n) → DeltaWord (suc n) n
degenWord i = degenW (positionFin i)

-- The standard generators-and-relations presentation of Δ.  These
-- are ALL simplicial identities, for arbitrary separated positions,
-- together with the ordinary category and congruence relations.
-- This is an independent definition: equality of its morphisms does
-- not assume completeness of a normal-form theorem.
data WordRelation : {m n : ℕ} → DeltaWord m n → DeltaWord m n → Type₀ where
  reflexive : {m n : ℕ} {f : DeltaWord m n} → WordRelation f f
  symmetric : {m n : ℕ} {f g : DeltaWord m n}
             → WordRelation f g → WordRelation g f
  transitive : {m n : ℕ} {f g h : DeltaWord m n}
              → WordRelation f g → WordRelation g h → WordRelation f h
  congruent : {m n k : ℕ} {f f' : DeltaWord m n} {g g' : DeltaWord n k}
             → WordRelation f f' → WordRelation g g'
             → WordRelation (seqW f g) (seqW f' g')
  identity-left : {m n : ℕ} (f : DeltaWord m n) → WordRelation (seqW idW f) f
  identity-right : {m n : ℕ} (f : DeltaWord m n) → WordRelation (seqW f idW) f
  associative : {m n k l : ℕ} (f : DeltaWord m n) (g : DeltaWord n k) (h : DeltaWord k l)
               → WordRelation (seqW (seqW f g) h) (seqW f (seqW g h))
  faces : {n : ℕ} (p : CoordinatePair (suc n))
         → WordRelation (seqW (faceWord (upper p)) (faceWord (lowerWide p)))
                        (seqW (faceWord (lower p)) (faceWord (upperWide p)))
  degens : {n : ℕ} (p : CoordinatePair n)
          → WordRelation (seqW (degenWord (lowerWide p)) (degenWord (upper p)))
                         (seqW (degenWord (upperWide p)) (degenWord (lower p)))
  same : {n : ℕ} (i : Position (suc n))
        → WordRelation (seqW (faceWord (weakenPosition i)) (degenWord i)) idW
  next : {n : ℕ} (i : Position (suc n))
        → WordRelation (seqW (faceWord (there i)) (degenWord i)) idW
  before : {n : ℕ} (p : CoordinatePair n)
           → WordRelation (seqW (faceWord (weakenPosition (lowerWide p))) (degenWord (upperWide p)))
                          (seqW (degenWord (upper p)) (faceWord (lowerWide p)))
  after : {n : ℕ} (p : CoordinatePair n)
          → WordRelation (seqW (faceWord (there (upperWide p))) (degenWord (lowerWide p)))
                         (seqW (degenWord (lower p)) (faceWord (upperWide p)))

PresentedMap : ℕ → ℕ → Type₀
PresentedMap m n = DeltaWord m n SQ./ WordRelation

presentedId : (n : ℕ) → PresentedMap n n
presentedId n = SQ.[ idW ]

infixl 20 _⋆p_
_⋆p_ : {m n k : ℕ} → PresentedMap m n → PresentedMap n k → PresentedMap m k
_⋆p_ = SQ.rec2 SQ.squash/
  (λ f g → SQ.[ seqW f g ])
  (λ f f' g p → SQ.eq/ _ _ (congruent p reflexive))
  (λ f g g' p → SQ.eq/ _ _ (congruent reflexive p))

DeltaPresentation : Category ℓ-zero ℓ-zero
Category.ob DeltaPresentation = ℕ
Category.Hom[_,_] DeltaPresentation = PresentedMap
Category.id DeltaPresentation {x = n} = presentedId n
Category._⋆_ DeltaPresentation = _⋆p_
Category.⋆IdL DeltaPresentation = SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ f → SQ.eq/ _ _ (identity-left f))
Category.⋆IdR DeltaPresentation = SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ f → SQ.eq/ _ _ (identity-right f))
Category.⋆Assoc DeltaPresentation = SQ.elimProp3 (λ _ _ _ → SQ.squash/ _ _)
  (λ f g h → SQ.eq/ _ _ (associative f g h))
Category.isSetHom DeltaPresentation = SQ.squash/

-- Each defining relation is checked against the concrete ordinal map.
evaluation-respects : {m n : ℕ} {f g : DeltaWord m n}
                    → WordRelation f g → evalWord f ≡ evalWord g
evaluation-respects reflexive = refl
evaluation-respects (symmetric p) = sym (evaluation-respects p)
evaluation-respects (transitive p q) = evaluation-respects p ∙ evaluation-respects q
evaluation-respects (congruent p q) = cong₂ _⋆o_ (evaluation-respects p) (evaluation-respects q)
evaluation-respects (identity-left f) = ordinalMapExt (λ _ → refl)
evaluation-respects (identity-right f) = ordinalMapExt (λ _ → refl)
evaluation-respects (associative f g h) = ordinalMapExt (λ _ → refl)
evaluation-respects (faces p) = ordinalMapExt (faces-law p)
evaluation-respects (degens p) = ordinalMapExt (degens-law p)
evaluation-respects (same i) = ordinalMapExt (same-law i)
evaluation-respects (next i) = ordinalMapExt (next-law i)
evaluation-respects (before p) = ordinalMapExt (before-law p)
evaluation-respects (after p) = ordinalMapExt (after-law p)

evaluatePresented : {m n : ℕ} → PresentedMap m n → OrdinalMap m n
evaluatePresented = SQ.rec isSetOrdinalMap evalWord (λ f g → evaluation-respects)

evaluation-compose : {m n k : ℕ} (f : PresentedMap m n) (g : PresentedMap n k)
                    → evaluatePresented (f ⋆p g) ≡ evaluatePresented f ⋆o evaluatePresented g
evaluation-compose = SQ.elimProp2 (λ _ _ → isSetOrdinalMap _ _)
  (λ _ _ → refl)

presentationEvaluation : Functor DeltaPresentation Delta
Functor.F-ob presentationEvaluation n = n
Functor.F-hom presentationEvaluation = evaluatePresented
Functor.F-id presentationEvaluation = refl
Functor.F-seq presentationEvaluation = evaluation-compose

-- Surjectivity follows from the independently checked decomposition.
-- Full faithfulness / injectivity is intentionally not asserted here.
presentation-surjective : {m n : ℕ} (f : OrdinalMap m n)
                       → Σ[ p ∈ PresentedMap m n ] evaluatePresented p ≡ f
presentation-surjective f = SQ.[ fst (normalizeOrdinal f) ] , snd (normalizeOrdinal f)
