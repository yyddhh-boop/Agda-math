{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.Presented where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (_^op)
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.NaturalTransformation.Base using (NatTrans)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (Position; here; there; weakenPosition;
  CoordinatePair; lower; upper; lowerWide; upperWide)
open import DHH.Simplicial.OrdinalLaws
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation

private variable ℓ : Level

positionFromFin : {n : ℕ} → Fin n → Position n
positionFromFin fzero = here
positionFromFin (fsuc i) = there (positionFromFin i)

position-from-to : {n : ℕ} (i : Position n) → positionFromFin (positionFin i) ≡ i
position-from-to here = refl
position-from-to (there i) = cong there (position-from-to i)

-- Equivalent standard presentation of a simplicial set by its faces,
-- degeneracies and ALL simplicial identities.  The laws below are
-- data to be supplied by the concrete construction, not postulates.
record PresentedSimplicialSet (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    cellsP : ℕ → hSet ℓ
    faceP : {n : ℕ} → Position (suc (suc n)) → fst (cellsP (suc n)) → fst (cellsP n)
    degenP : {n : ℕ} → Position (suc n) → fst (cellsP n) → fst (cellsP (suc n))
    facesP : {n : ℕ} (p : CoordinatePair (suc n)) (c : fst (cellsP (suc (suc n))))
           → faceP (upper p) (faceP (lowerWide p) c)
           ≡ faceP (lower p) (faceP (upperWide p) c)
    degensP : {n : ℕ} (p : CoordinatePair n) (c : fst (cellsP n))
            → degenP (lowerWide p) (degenP (upper p) c)
            ≡ degenP (upperWide p) (degenP (lower p) c)
    sameP : {n : ℕ} (i : Position (suc n)) (c : fst (cellsP n))
          → faceP (weakenPosition i) (degenP i c) ≡ c
    nextP : {n : ℕ} (i : Position (suc n)) (c : fst (cellsP n))
          → faceP (there i) (degenP i c) ≡ c
    beforeP : {n : ℕ} (p : CoordinatePair n) (c : fst (cellsP (suc n)))
            → faceP (weakenPosition (lowerWide p)) (degenP (upperWide p) c)
            ≡ degenP (upper p) (faceP (lowerWide p) c)
    afterP : {n : ℕ} (p : CoordinatePair n) (c : fst (cellsP (suc n)))
           → faceP (there (upperWide p)) (degenP (lowerWide p) c)
           ≡ degenP (lower p) (faceP (upperWide p) c)
open PresentedSimplicialSet public

PCell : PresentedSimplicialSet ℓ → ℕ → Type ℓ
PCell A n = fst (cellsP A n)

actWord : {m n : ℕ} (A : PresentedSimplicialSet ℓ) → DeltaWord m n → PCell A n → PCell A m
actWord A idW c = c
actWord A (faceW i) c = faceP A (positionFromFin i) c
actWord A (degenW i) c = degenP A (positionFromFin i) c
actWord A (seqW f g) c = actWord A f (actWord A g c)

face-action : {n : ℕ} (A : PresentedSimplicialSet ℓ)
              (i : Position (suc (suc n))) (c : PCell A (suc n))
            → actWord A (faceWord i) c ≡ faceP A i c
face-action A i c = cong (λ j → faceP A j c) (position-from-to i)

degen-action : {n : ℕ} (A : PresentedSimplicialSet ℓ)
               (i : Position (suc n)) (c : PCell A n)
             → actWord A (degenWord i) c ≡ degenP A i c
degen-action A i c = cong (λ j → degenP A j c) (position-from-to i)

two-faces : {n : ℕ} (A : PresentedSimplicialSet ℓ)
             (i : Position (suc (suc n))) (j : Position (suc (suc (suc n))))
             (c : PCell A (suc (suc n)))
           → actWord A (seqW (faceWord i) (faceWord j)) c ≡ faceP A i (faceP A j c)
two-faces A i j c = face-action A i _ ∙ cong (faceP A i) (face-action A j c)

two-degens : {n : ℕ} (A : PresentedSimplicialSet ℓ)
              (i : Position (suc (suc n))) (j : Position (suc n)) (c : PCell A n)
            → actWord A (seqW (degenWord i) (degenWord j)) c ≡ degenP A i (degenP A j c)
two-degens A i j c = degen-action A i _ ∙ cong (degenP A i) (degen-action A j c)

face-degen : {n : ℕ} (A : PresentedSimplicialSet ℓ)
              (i : Position (suc (suc n))) (j : Position (suc n)) (c : PCell A n)
            → actWord A (seqW (faceWord i) (degenWord j)) c ≡ faceP A i (degenP A j c)
face-degen A i j c = face-action A i _ ∙ cong (faceP A i) (degen-action A j c)

degen-face : {n : ℕ} (A : PresentedSimplicialSet ℓ)
              (i : Position (suc n)) (j : Position (suc (suc n))) (c : PCell A (suc n))
            → actWord A (seqW (degenWord i) (faceWord j)) c ≡ degenP A i (faceP A j c)
degen-face A i j c = degen-action A i _ ∙ cong (degenP A i) (face-action A j c)

action-respects : {m n : ℕ} (A : PresentedSimplicialSet ℓ) {f g : DeltaWord m n}
                  → WordRelation f g → (c : PCell A n) → actWord A f c ≡ actWord A g c
action-respects A reflexive c = refl
action-respects A (symmetric p) c = sym (action-respects A p c)
action-respects A (transitive p q) c = action-respects A p c ∙ action-respects A q c
action-respects A (congruent {f = f} {g' = g'} p q) c =
  cong (actWord A f) (action-respects A q c) ∙ action-respects A p (actWord A g' c)
action-respects A (identity-left f) c = refl
action-respects A (identity-right f) c = refl
action-respects A (associative f g h) c = refl
action-respects A (faces p) c =
  two-faces A (upper p) (lowerWide p) c ∙ facesP A p c
  ∙ sym (two-faces A (lower p) (upperWide p) c)
action-respects A (degens p) c =
  two-degens A (lowerWide p) (upper p) c ∙ degensP A p c
  ∙ sym (two-degens A (upperWide p) (lower p) c)
action-respects A (same i) c = face-degen A (weakenPosition i) i c ∙ sameP A i c
action-respects A (next i) c = face-degen A (there i) i c ∙ nextP A i c
action-respects A (before p) c =
  face-degen A (weakenPosition (lowerWide p)) (upperWide p) c ∙ beforeP A p c
  ∙ sym (degen-face A (upper p) (lowerWide p) c)
action-respects A (after p) c =
  face-degen A (there (upperWide p)) (lowerWide p) c ∙ afterP A p c
  ∙ sym (degen-face A (lower p) (upperWide p) c)

actPresented : {m n : ℕ} (A : PresentedSimplicialSet ℓ) → PresentedMap m n → PCell A n → PCell A m
actPresented {m = m} A = SQ.rec (isSetΠ (λ _ → snd (cellsP A m)))
  (actWord A) (λ f g p → funExt (action-respects A p))

action-compose : {m n k : ℕ} (A : PresentedSimplicialSet ℓ)
                  (f : PresentedMap m n) (g : PresentedMap n k)
                → actPresented A (f ⋆p g) ≡ (λ c → actPresented A f (actPresented A g c))
action-compose {m = m} A = SQ.elimProp2
  (λ _ _ → isSetΠ (λ _ → snd (cellsP A m)) _ _) (λ _ _ → refl)

presentedPresheaf : PresentedSimplicialSet ℓ → Functor (DeltaPresentation ^op) (SET ℓ)
Functor.F-ob (presentedPresheaf A) = cellsP A
Functor.F-hom (presentedPresheaf A) = actPresented A
Functor.F-id (presentedPresheaf A) = refl
Functor.F-seq (presentedPresheaf A) f g = action-compose A g f

-- Maps of the presented simplicial sets.  Naturality for the two
-- generators suffices because the action on every word is recursive.
record PresentedNatural (A B : PresentedSimplicialSet ℓ) : Type ℓ where
  field
    mapPCell : (n : ℕ) → PCell A n → PCell B n
    face-naturalP : {n : ℕ} (i : Position (suc (suc n))) (c : PCell A (suc n))
                   → mapPCell n (faceP A i c) ≡ faceP B i (mapPCell (suc n) c)
    degen-naturalP : {n : ℕ} (i : Position (suc n)) (c : PCell A n)
                    → mapPCell (suc n) (degenP A i c) ≡ degenP B i (mapPCell n c)
open PresentedNatural public

word-naturalP : {A B : PresentedSimplicialSet ℓ} (η : PresentedNatural A B)
                {m n : ℕ} (w : DeltaWord m n) (c : PCell A n)
              → mapPCell η m (actWord A w c) ≡ actWord B w (mapPCell η n c)
word-naturalP η idW c = refl
word-naturalP η (faceW i) c = face-naturalP η (positionFromFin i) c
word-naturalP η (degenW i) c = degen-naturalP η (positionFromFin i) c
word-naturalP {A = A} {B = B} η (seqW f g) c =
  word-naturalP η f (actWord A g c) ∙ cong (actWord B f) (word-naturalP η g c)

presented-naturalP : {A B : PresentedSimplicialSet ℓ} (η : PresentedNatural A B)
                    {m n : ℕ} (u : PresentedMap m n)
                  → (λ c → mapPCell η m (actPresented A u c))
                  ≡ (λ c → actPresented B u (mapPCell η n c))
presented-naturalP {B = B} η {m = m} = SQ.elimProp
  (λ _ → isSetΠ (λ _ → snd (cellsP B m)) _ _)
  (λ w → funExt (word-naturalP η w))

presentedNaturalTransformation : {A B : PresentedSimplicialSet ℓ}
                              → PresentedNatural A B
                              → NatTrans (presentedPresheaf A) (presentedPresheaf B)
NatTrans.N-ob (presentedNaturalTransformation η) = mapPCell η
NatTrans.N-hom (presentedNaturalTransformation η) = presented-naturalP η

presentedIdentity : (A : PresentedSimplicialSet ℓ) → PresentedNatural A A
mapPCell (presentedIdentity A) n c = c
face-naturalP (presentedIdentity A) i c = refl
degen-naturalP (presentedIdentity A) i c = refl

presentedCompose : {A B C : PresentedSimplicialSet ℓ}
                  → PresentedNatural A B → PresentedNatural B C → PresentedNatural A C
mapPCell (presentedCompose f g) n c = mapPCell g n (mapPCell f n c)
face-naturalP (presentedCompose f g) {n = n} i c =
  cong (mapPCell g n) (face-naturalP f i c) ∙ face-naturalP g i (mapPCell f _ c)
degen-naturalP (presentedCompose f g) {n = n} i c =
  cong (mapPCell g (suc n)) (degen-naturalP f i c) ∙ degen-naturalP g i (mapPCell f n c)
