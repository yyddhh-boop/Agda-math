{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import DHH.Simplicial.Ordinal

private variable ℓ ℓ' ℓ'' : Level

-- SET-valued presheaves on the complete simplex category Δ.
record SimplicialSet (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    simplices : ℕ → hSet ℓ
    reindexΔ : {m n : ℕ} → OrdinalMap m n → fst (simplices n) → fst (simplices m)
    reindexΔ-id : {n : ℕ} (c : fst (simplices n)) → reindexΔ (ordinalId n) c ≡ c
    reindexΔ-compose : {m n k : ℕ} (f : OrdinalMap m n) (g : OrdinalMap n k)
                      (c : fst (simplices k))
                    → reindexΔ (f ⋆o g) c ≡ reindexΔ f (reindexΔ g c)
open SimplicialSet public

Simplex : SimplicialSet ℓ → ℕ → Type ℓ
Simplex A n = fst (simplices A n)

record SimplicialNatural (A : SimplicialSet ℓ) (B : SimplicialSet ℓ')
                        : Type (ℓ-max ℓ ℓ') where
  field
    mapSimplex : (n : ℕ) → Simplex A n → Simplex B n
    naturalΔ : {m n : ℕ} (f : OrdinalMap m n) (c : Simplex A n)
             → mapSimplex m (reindexΔ A f c) ≡ reindexΔ B f (mapSimplex n c)
open SimplicialNatural public

simplicialNaturalExt : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                       {f g : SimplicialNatural A B}
                     → ((n : ℕ) (c : Simplex A n) → mapSimplex f n c ≡ mapSimplex g n c)
                     → f ≡ g
mapSimplex (simplicialNaturalExt p i) n c = p n c i
naturalΔ (simplicialNaturalExt {A = A} {B = B} {f = f} {g = g} p i) {m} {n} u c =
  isProp→PathP
    {B = λ j → p m (reindexΔ A u c) j ≡ reindexΔ B u (p n c j)}
    (λ j → snd (simplices B m) _ _)
    (naturalΔ f u c) (naturalΔ g u c) i

simplicialId : (A : SimplicialSet ℓ) → SimplicialNatural A A
mapSimplex (simplicialId A) n c = c
naturalΔ (simplicialId A) u c = refl

infixl 20 _⋆s_
_⋆s_ : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} {C : SimplicialSet ℓ''}
       → SimplicialNatural A B → SimplicialNatural B C → SimplicialNatural A C
mapSimplex (f ⋆s g) n c = mapSimplex g n (mapSimplex f n c)
naturalΔ (f ⋆s g) {m} u c =
  cong (mapSimplex g m) (naturalΔ f u c) ∙ naturalΔ g u (mapSimplex f _ c)

NaturalProofΔ : (A : SimplicialSet ℓ) (B : SimplicialSet ℓ')
              → ((n : ℕ) → Simplex A n → Simplex B n) → Type (ℓ-max ℓ ℓ')
NaturalProofΔ A B f = (m n : ℕ) (u : OrdinalMap m n) (c : Simplex A n)
                    → f m (reindexΔ A u c) ≡ reindexΔ B u (f n c)

naturalProofΔ-isProp : (A : SimplicialSet ℓ) (B : SimplicialSet ℓ')
                      (f : (n : ℕ) → Simplex A n → Simplex B n)
                    → isProp (NaturalProofΔ A B f)
naturalProofΔ-isProp A B f = isPropΠ λ m → isPropΠ λ n →
  isPropΠ λ u → isPropΠ λ c → snd (simplices B m) _ _

NaturalΣΔ : (A : SimplicialSet ℓ) (B : SimplicialSet ℓ') → Type (ℓ-max ℓ ℓ')
NaturalΣΔ A B = Σ[ f ∈ ((n : ℕ) → Simplex A n → Simplex B n) ] NaturalProofΔ A B f

naturalToΣΔ : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
              → SimplicialNatural A B → NaturalΣΔ A B
naturalToΣΔ f = mapSimplex f , λ m n u c → naturalΔ f u c

ΣToNaturalΔ : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
              → NaturalΣΔ A B → SimplicialNatural A B
mapSimplex (ΣToNaturalΔ (f , p)) = f
naturalΔ (ΣToNaturalΔ (f , p)) {m} {n} = p m n

isSetSimplicialNatural : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                      → isSet (SimplicialNatural A B)
isSetSimplicialNatural {A = A} {B = B} =
  isSetRetract naturalToΣΔ ΣToNaturalΔ (λ f → simplicialNaturalExt (λ _ _ → refl))
    (isSetΣSndProp (isSetΠ2 (λ n _ → snd (simplices B n)))
      (naturalProofΔ-isProp A B))

SimplicialSetCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (SimplicialSetCategory ℓ) = SimplicialSet ℓ
Category.Hom[_,_] (SimplicialSetCategory ℓ) = SimplicialNatural
Category.id (SimplicialSetCategory ℓ) {x = A} = simplicialId A
Category._⋆_ (SimplicialSetCategory ℓ) = _⋆s_
Category.⋆IdL (SimplicialSetCategory ℓ) f = simplicialNaturalExt (λ _ _ → refl)
Category.⋆IdR (SimplicialSetCategory ℓ) f = simplicialNaturalExt (λ _ _ → refl)
Category.⋆Assoc (SimplicialSetCategory ℓ) f g h = simplicialNaturalExt (λ _ _ → refl)
Category.isSetHom (SimplicialSetCategory ℓ) = isSetSimplicialNatural

faceΔ : {n : ℕ} (A : SimplicialSet ℓ) → Fin (suc (suc n))
       → Simplex A (suc n) → Simplex A n
faceΔ A i = reindexΔ A (coface i)

degeneracyΔ : {n : ℕ} (A : SimplicialSet ℓ) → Fin (suc n)
             → Simplex A n → Simplex A (suc n)
degeneracyΔ A i = reindexΔ A (codegeneracy i)

RepresentableSimplex : ℕ → SimplicialSet ℓ-zero
simplices (RepresentableSimplex n) m = OrdinalMap m n , isSetOrdinalMap
reindexΔ (RepresentableSimplex n) f g = f ⋆o g
reindexΔ-id (RepresentableSimplex n) g = Category.⋆IdL Delta g
reindexΔ-compose (RepresentableSimplex n) f g h = Category.⋆Assoc Delta f g h

classifySimplex : {n : ℕ} (A : SimplicialSet ℓ) (c : Simplex A n)
                → SimplicialNatural (RepresentableSimplex n) A
mapSimplex (classifySimplex A c) m u = reindexΔ A u c
naturalΔ (classifySimplex A c) f g = reindexΔ-compose A f g c

simplex-classifier-evaluation : {n : ℕ} (A : SimplicialSet ℓ) (c : Simplex A n)
                            → mapSimplex (classifySimplex A c) n (ordinalId n) ≡ c
simplex-classifier-evaluation A c = reindexΔ-id A c

every-natural-simplex-classified : {n : ℕ} (A : SimplicialSet ℓ)
                                 (η : SimplicialNatural (RepresentableSimplex n) A)
                               → classifySimplex A (mapSimplex η n (ordinalId n)) ≡ η
every-natural-simplex-classified {n = n} A η = simplicialNaturalExt λ m u →
  sym (naturalΔ η u (ordinalId n)) ∙ cong (mapSimplex η m) (Category.⋆IdR Delta u)
