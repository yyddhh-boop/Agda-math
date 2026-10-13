{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.PresentationShift where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (Position; here; there; under; front)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.OrdinalLaws
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation

-- Adding a new least element is well-defined on the independently
-- presented category: each original relation is sent to an ORIGINAL
-- simplicial relation at shifted coordinates, never to semantic equality.
lift-relation : {m n : ℕ} {f g : DeltaWord m n}
              → WordRelation f g → WordRelation (liftWord f) (liftWord g)
lift-relation reflexive = reflexive
lift-relation (symmetric p) = symmetric (lift-relation p)
lift-relation (transitive p q) = transitive (lift-relation p) (lift-relation q)
lift-relation (congruent p q) = congruent (lift-relation p) (lift-relation q)
lift-relation (identity-left f) = identity-left (liftWord f)
lift-relation (identity-right f) = identity-right (liftWord f)
lift-relation (associative f g h) = associative (liftWord f) (liftWord g) (liftWord h)
lift-relation (faces p) = faces (under p)
lift-relation (degens p) = degens (under p)
lift-relation (same i) = same (there i)
lift-relation (next i) = next (there i)
lift-relation (before p) = before (under p)
lift-relation (after p) = after (under p)

liftPresented : {m n : ℕ} → PresentedMap m n → PresentedMap (suc m) (suc n)
liftPresented = SQ.rec SQ.squash/ (λ w → SQ.[ liftWord w ])
  (λ f g p → SQ.eq/ _ _ (lift-relation p))

liftPresented-compose : {m n k : ℕ} (f : PresentedMap m n) (g : PresentedMap n k)
  → liftPresented (f ⋆p g) ≡ liftPresented f ⋆p liftPresented g
liftPresented-compose = SQ.elimProp2 (λ _ _ → SQ.squash/ _ _) (λ _ _ → refl)

presentationShift : Functor DeltaPresentation DeltaPresentation
Functor.F-ob presentationShift = suc
Functor.F-hom presentationShift = liftPresented
Functor.F-id presentationShift = refl
Functor.F-seq presentationShift = liftPresented-compose

evaluation-liftPresented : {m n : ℕ} (p : PresentedMap m n)
  → evaluatePresented (liftPresented p) ≡ liftOrdinal (evaluatePresented p)
evaluation-liftPresented = SQ.elimProp (λ _ → isSetOrdinalMap _ _) lift-evaluation

finPosition : {n : ℕ} → Fin n → Position n
finPosition fzero = here
finPosition (fsuc i) = there (finPosition i)
fin-position-inverse : {n : ℕ} (i : Fin n) → positionFin (finPosition i) ≡ i
fin-position-inverse fzero = refl
fin-position-inverse (fsuc i) = cong fsuc (fin-position-inverse i)

head-inclusion-word : {m n : ℕ} (w : DeltaWord m n)
  → SQ.[ seqW (faceW fzero) (liftWord w) ]
    ≡ SQ.[ seqW w (faceW fzero) ]
head-inclusion-word idW =
  SQ.eq/ _ _ (identity-right (faceW fzero))
  ∙ sym (SQ.eq/ _ _ (identity-left (faceW fzero)))
head-inclusion-word (faceW i) =
  cong (λ j → SQ.[ seqW (faceW fzero) (faceW (fsuc j)) ])
    (sym (fin-position-inverse i))
  ∙ SQ.eq/ _ _ (symmetric (faces (front (finPosition i))))
  ∙ cong (λ j → SQ.[ seqW (faceW j) (faceW fzero) ]) (fin-position-inverse i)
head-inclusion-word (degenW i) =
  cong (λ j → SQ.[ seqW (faceW fzero) (degenW (fsuc j)) ])
    (sym (fin-position-inverse i))
  ∙ SQ.eq/ _ _ (before (front (finPosition i)))
  ∙ cong (λ j → SQ.[ seqW (degenW j) (faceW fzero) ]) (fin-position-inverse i)
head-inclusion-word (seqW f g) =
  sym (Category.⋆Assoc DeltaPresentation SQ.[ faceW fzero ] SQ.[ liftWord f ] SQ.[ liftWord g ])
  ∙ cong (λ h → h ⋆p SQ.[ liftWord g ]) (head-inclusion-word f)
  ∙ Category.⋆Assoc DeltaPresentation SQ.[ f ] SQ.[ faceW fzero ] SQ.[ liftWord g ]
  ∙ cong (SQ.[ f ] ⋆p_) (head-inclusion-word g)
  ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ f ] SQ.[ g ] SQ.[ faceW fzero ])

head-inclusion-natural : {m n : ℕ} (p : PresentedMap m n)
  → SQ.[ faceW fzero ] ⋆p liftPresented p ≡ p ⋆p SQ.[ faceW fzero ]
head-inclusion-natural = SQ.elimProp (λ _ → SQ.squash/ _ _) head-inclusion-word
