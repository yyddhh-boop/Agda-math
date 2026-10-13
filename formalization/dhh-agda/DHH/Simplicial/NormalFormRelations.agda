{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.NormalFormRelations where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Categories.Category.Base using (Category)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (here; there; under; front)
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation
open import DHH.Simplicial.PresentationShift
open import DHH.Simplicial.NormalForm

vertex-face : (n : ℕ) (i : Fin (suc n))
  → SQ.[ vertexWord n ] ⋆p SQ.[ faceW (fsuc i) ] ≡ SQ.[ vertexWord (suc n) ]
vertex-face zero fzero = refl
vertex-face (suc n) fzero = refl
vertex-face (suc n) (fsuc i) =
  Category.⋆Assoc DeltaPresentation SQ.[ vertexWord n ] SQ.[ faceW (fsuc fzero) ] SQ.[ faceW (fsuc (fsuc i)) ]
  ∙ cong (SQ.[ vertexWord n ] ⋆p_)
    (cong (λ j → SQ.[ seqW (faceW (fsuc fzero)) (faceW (fsuc (fsuc j))) ]) (sym (fin-position-inverse i))
    ∙ SQ.eq/ _ _ (symmetric (faces (under (front (finPosition i)))))
    ∙ cong (λ j → SQ.[ seqW (faceW (fsuc j)) (faceW (fsuc fzero)) ]) (fin-position-inverse i))
  ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ vertexWord n ] SQ.[ faceW (fsuc i) ] SQ.[ faceW (fsuc fzero) ])
  ∙ cong (_⋆p SQ.[ faceW (fsuc fzero) ]) (vertex-face n i)

vertex-degen : (n : ℕ) (i : Fin (suc n))
  → SQ.[ vertexWord (suc n) ] ⋆p SQ.[ degenW i ] ≡ SQ.[ vertexWord n ]
vertex-degen n fzero =
  Category.⋆Assoc DeltaPresentation SQ.[ vertexWord n ] SQ.[ faceW (fsuc fzero) ] SQ.[ degenW fzero ]
  ∙ cong (SQ.[ vertexWord n ] ⋆p_) (SQ.eq/ _ _ (next here))
  ∙ Category.⋆IdR DeltaPresentation SQ.[ vertexWord n ]
vertex-degen (suc n) (fsuc fzero) =
  Category.⋆Assoc DeltaPresentation SQ.[ vertexWord (suc n) ] SQ.[ faceW (fsuc fzero) ] SQ.[ degenW (fsuc fzero) ]
  ∙ cong (SQ.[ vertexWord (suc n) ] ⋆p_) (SQ.eq/ _ _ (same (there here)))
  ∙ Category.⋆IdR DeltaPresentation SQ.[ vertexWord (suc n) ]
vertex-degen (suc (suc n)) (fsuc (fsuc i)) =
  Category.⋆Assoc DeltaPresentation SQ.[ vertexWord (suc (suc n)) ] SQ.[ faceW (fsuc fzero) ] SQ.[ degenW (fsuc (fsuc i)) ]
  ∙ cong (SQ.[ vertexWord (suc (suc n)) ] ⋆p_)
    (cong (λ j → SQ.[ seqW (faceW (fsuc fzero)) (degenW (fsuc (fsuc j))) ]) (sym (fin-position-inverse i))
    ∙ SQ.eq/ _ _ (before (under (front (finPosition i))))
    ∙ cong (λ j → SQ.[ seqW (degenW (fsuc j)) (faceW (fsuc fzero)) ]) (fin-position-inverse i))
  ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ vertexWord (suc (suc n)) ] SQ.[ degenW (fsuc i) ] SQ.[ faceW (fsuc fzero) ])
  ∙ cong (_⋆p SQ.[ faceW (fsuc fzero) ]) (vertex-degen (suc n) (fsuc i))

-- The first collapse commutes with a DOUBLE shift for every word.
-- It is not falsely asserted to commute with a single shift of an
-- arbitrary word (which would fail for a word with nonzero first value).
double-shift-collapse : {m n : ℕ} (w : DeltaWord m n)
  → SQ.[ liftWord (liftWord w) ] ⋆p SQ.[ degenW fzero ]
    ≡ SQ.[ degenW fzero ] ⋆p SQ.[ liftWord w ]
double-shift-collapse idW = Category.⋆IdL DeltaPresentation SQ.[ degenW fzero ]
  ∙ sym (Category.⋆IdR DeltaPresentation SQ.[ degenW fzero ])
double-shift-collapse (faceW i) =
  cong (λ j → SQ.[ seqW (faceW (fsuc (fsuc j))) (degenW fzero) ]) (sym (fin-position-inverse i))
  ∙ SQ.eq/ _ _ (after (front (finPosition i)))
  ∙ cong (λ j → SQ.[ seqW (degenW fzero) (faceW (fsuc j)) ]) (fin-position-inverse i)
double-shift-collapse (degenW i) =
  cong (λ j → SQ.[ seqW (degenW (fsuc (fsuc j))) (degenW fzero) ]) (sym (fin-position-inverse i))
  ∙ SQ.eq/ _ _ (symmetric (degens (front (there (finPosition i)))))
  ∙ cong (λ j → SQ.[ seqW (degenW fzero) (degenW (fsuc j)) ]) (fin-position-inverse i)
double-shift-collapse (seqW f g) =
  Category.⋆Assoc DeltaPresentation SQ.[ liftWord (liftWord f) ] SQ.[ liftWord (liftWord g) ] SQ.[ degenW fzero ]
  ∙ cong (SQ.[ liftWord (liftWord f) ] ⋆p_) (double-shift-collapse g)
  ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ liftWord (liftWord f) ] SQ.[ degenW fzero ] SQ.[ liftWord g ])
  ∙ cong (_⋆p SQ.[ liftWord g ]) (double-shift-collapse f)
  ∙ Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ] SQ.[ liftWord f ] SQ.[ liftWord g ]

vertex-shift-collapse : (n : ℕ)
  → SQ.[ liftWord (vertexWord n) ] ⋆p SQ.[ degenW fzero ]
    ≡ SQ.[ degenW fzero ] ⋆p SQ.[ vertexWord n ]
vertex-shift-collapse zero = Category.⋆IdL DeltaPresentation SQ.[ degenW fzero ]
  ∙ sym (Category.⋆IdR DeltaPresentation SQ.[ degenW fzero ])
vertex-shift-collapse (suc n) =
  Category.⋆Assoc DeltaPresentation SQ.[ liftWord (vertexWord n) ] SQ.[ faceW (fsuc (fsuc fzero)) ] SQ.[ degenW fzero ]
  ∙ cong (SQ.[ liftWord (vertexWord n) ] ⋆p_) (SQ.eq/ _ _ (after (front here)))
  ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ liftWord (vertexWord n) ] SQ.[ degenW fzero ] SQ.[ faceW (fsuc fzero) ])
  ∙ cong (_⋆p SQ.[ faceW (fsuc fzero) ]) (vertex-shift-collapse n)
  ∙ Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ] SQ.[ vertexWord n ] SQ.[ faceW (fsuc fzero) ]

zero-shift-collapse : {m n : ℕ} (z : ZeroNormal m n)
  → SQ.[ liftWord (zeroWord z) ] ⋆p SQ.[ degenW fzero ]
    ≡ SQ.[ degenW fzero ] ⋆p SQ.[ zeroWord z ]
zero-shift-collapse {n = n} zvertex = vertex-shift-collapse n
zero-shift-collapse (zrepeat z) =
  Category.⋆Assoc DeltaPresentation SQ.[ degenW (fsuc fzero) ] SQ.[ liftWord (zeroWord z) ] SQ.[ degenW fzero ]
  ∙ cong (SQ.[ degenW (fsuc fzero) ] ⋆p_) (zero-shift-collapse z)
  ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ degenW (fsuc fzero) ] SQ.[ degenW fzero ] SQ.[ zeroWord z ])
  ∙ cong (_⋆p SQ.[ zeroWord z ]) (SQ.eq/ _ _ (symmetric (degens (front here))))
  ∙ Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ] SQ.[ degenW fzero ] SQ.[ zeroWord z ]
zero-shift-collapse (zlift q) = double-shift-collapse (normalWord q)
