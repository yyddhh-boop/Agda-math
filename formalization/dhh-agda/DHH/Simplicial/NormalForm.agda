{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.NormalForm where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; znots; injSucFin) renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Empty as Empty
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Word

-- A zero-head form separates repetitions of the first vertex from
-- strict movement to the positive tail.  Both mutually recursive
-- trees support structural recursion on proper subtrees.  nzero is a
-- same-dimension wrapper; zvertex ends the tree, and nshift/zrepeat/zlift
-- reduce dimensions when descending to their recursive arguments.
mutual
  data Normal : ℕ → ℕ → Type₀ where
    nzero : {m n : ℕ} → ZeroNormal m n → Normal m n
    nshift : {m n : ℕ} → Normal m n → Normal m (suc n)
  data ZeroNormal : ℕ → ℕ → Type₀ where
    zvertex : {n : ℕ} → ZeroNormal zero n
    zrepeat : {m n : ℕ} → ZeroNormal m n → ZeroNormal (suc m) n
    zlift : {m n : ℕ} → Normal m n → ZeroNormal (suc m) (suc n)

vertexWord : (n : ℕ) → DeltaWord zero n
vertexWord zero = idW
vertexWord (suc n) = seqW (vertexWord n) (faceW (fsuc fzero))

mutual
  normalWord : {m n : ℕ} → Normal m n → DeltaWord m n
  normalWord (nzero z) = zeroWord z
  normalWord (nshift q) = seqW (normalWord q) (faceW fzero)
  zeroWord : {m n : ℕ} → ZeroNormal m n → DeltaWord m n
  zeroWord {n = n} zvertex = vertexWord n
  zeroWord (zrepeat z) = seqW (degenW fzero) (zeroWord z)
  zeroWord (zlift q) = liftWord (normalWord q)

mutual
  normalSemantics : {m n : ℕ} → Normal m n → OrdinalMap m n
  normalSemantics (nzero z) = zeroSemantics z
  normalSemantics (nshift q) = normalSemantics q ⋆o coface fzero
  zeroSemantics : {m n : ℕ} → ZeroNormal m n → OrdinalMap m n
  zeroSemantics {n = n} zvertex = constantZeroOrdinal zero n
  zeroSemantics (zrepeat z) = codegeneracy fzero ⋆o zeroSemantics z
  zeroSemantics (zlift q) = liftOrdinal (normalSemantics q)

zero-head : {m n : ℕ} (z : ZeroNormal m n)
  → mapIndex (zeroSemantics z) fzero ≡ fzero
zero-head zvertex = refl
zero-head (zrepeat z) = zero-head z
zero-head (zlift q) = refl

vertex-word-head : (n : ℕ) → mapIndex (evalWord (vertexWord n)) fzero ≡ fzero
vertex-word-head zero = refl
vertex-word-head (suc n) = cong (skip (fsuc fzero)) (vertex-word-head n)

mutual
  normal-word-evaluation : {m n : ℕ} (q : Normal m n)
    → evalWord (normalWord q) ≡ normalSemantics q
  normal-word-evaluation (nzero z) = zero-word-evaluation z
  normal-word-evaluation (nshift q) = cong (_⋆o coface fzero) (normal-word-evaluation q)
  zero-word-evaluation : {m n : ℕ} (z : ZeroNormal m n)
    → evalWord (zeroWord z) ≡ zeroSemantics z
  zero-word-evaluation {n = n} zvertex = ordinalMapExt λ x →
    cong (mapIndex (evalWord (vertexWord n))) (singletonIndex x) ∙ vertex-word-head n
  zero-word-evaluation (zrepeat z) = cong (codegeneracy fzero ⋆o_) (zero-word-evaluation z)
  zero-word-evaluation (zlift q) = lift-evaluation (normalWord q)
    ∙ cong liftOrdinal (normal-word-evaluation q)

-- Semantic injectivity is a structural proof: the first value separates
-- nzero/nshift, and the second value separates zrepeat/zlift.
mutual
  normal-semantic-injective : {m n : ℕ} (q r : Normal m n)
    → normalSemantics q ≡ normalSemantics r → q ≡ r
  normal-semantic-injective (nzero z) (nzero w) e = cong nzero (zero-semantic-injective z w e)
  normal-semantic-injective (nzero z) (nshift r) e = Empty.rec
    (znots (sym (zero-head z) ∙ cong (λ f → mapIndex f fzero) e))
  normal-semantic-injective (nshift q) (nzero w) e = Empty.rec
    (znots (sym (zero-head w) ∙ cong (λ f → mapIndex f fzero) (sym e)))
  normal-semantic-injective (nshift q) (nshift r) e = cong nshift
    (normal-semantic-injective q r (ordinalMapExt λ x →
      injSucFin (cong (λ f → mapIndex f x) e)))

  zero-semantic-injective : {m n : ℕ} (z w : ZeroNormal m n)
    → zeroSemantics z ≡ zeroSemantics w → z ≡ w
  zero-semantic-injective zvertex zvertex e = refl
  zero-semantic-injective (zrepeat z) (zrepeat w) e = cong zrepeat
    (zero-semantic-injective z w (ordinalMapExt λ x →
      cong (λ f → mapIndex f (fsuc x)) e))
  zero-semantic-injective (zrepeat z) (zlift r) e = Empty.rec
    (znots (sym (zero-head z) ∙ cong (λ f → mapIndex f (fsuc fzero)) e))
  zero-semantic-injective (zlift q) (zrepeat w) e = Empty.rec
    (znots (sym (zero-head w) ∙ cong (λ f → mapIndex f (fsuc fzero)) (sym e)))
  zero-semantic-injective (zlift q) (zlift r) e = cong zlift
    (normal-semantic-injective q r (ordinalMapExt λ x →
      injSucFin (cong (λ f → mapIndex f (fsuc x)) e)))
