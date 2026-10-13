{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.PresentedCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import DHH.Cubes using (Position)
open import DHH.Simplicial.Presented

private variable ℓ : Level

-- Every naturality field is an equality in a set.  Consequently a map
-- is determined by its degreewise functions, including its proof fields.
presentedNaturalExt : {A B : PresentedSimplicialSet ℓ}
                      {f g : PresentedNatural A B}
                    → ((n : ℕ) (c : PCell A n) → mapPCell f n c ≡ mapPCell g n c)
                    → f ≡ g
mapPCell (presentedNaturalExt p j) n c = p n c j
face-naturalP (presentedNaturalExt {A = A} {B = B} {f = f} {g = g} p j) {n} i c =
  isProp→PathP
    {B = λ k → p n (faceP A i c) k ≡ faceP B i (p (suc n) c k)}
    (λ _ → snd (cellsP B n) _ _)
    (face-naturalP f i c) (face-naturalP g i c) j
degen-naturalP (presentedNaturalExt {A = A} {B = B} {f = f} {g = g} p j) {n} i c =
  isProp→PathP
    {B = λ k → p (suc n) (degenP A i c) k ≡ degenP B i (p n c k)}
    (λ _ → snd (cellsP B (suc n)) _ _)
    (degen-naturalP f i c) (degen-naturalP g i c) j

private
  NaturalProofP : (A B : PresentedSimplicialSet ℓ)
                → ((n : ℕ) → PCell A n → PCell B n) → Type ℓ
  NaturalProofP A B f =
    ((n : ℕ) (i : Position (suc (suc n))) (c : PCell A (suc n))
      → f n (faceP A i c) ≡ faceP B i (f (suc n) c))
    × ((n : ℕ) (i : Position (suc n)) (c : PCell A n)
      → f (suc n) (degenP A i c) ≡ degenP B i (f n c))

  naturalProofP-isProp : (A B : PresentedSimplicialSet ℓ)
                        (f : (n : ℕ) → PCell A n → PCell B n)
                      → isProp (NaturalProofP A B f)
  naturalProofP-isProp A B f = isProp×
    (isPropΠ3 λ n _ _ → snd (cellsP B n) _ _)
    (isPropΠ3 λ n _ _ → snd (cellsP B (suc n)) _ _)

  NaturalΣP : (A B : PresentedSimplicialSet ℓ) → Type ℓ
  NaturalΣP A B = Σ[ f ∈ ((n : ℕ) → PCell A n → PCell B n) ] NaturalProofP A B f

  naturalToΣP : {A B : PresentedSimplicialSet ℓ}
              → PresentedNatural A B → NaturalΣP A B
  naturalToΣP f = mapPCell f ,
    (λ n → face-naturalP f {n = n}) , (λ n → degen-naturalP f {n = n})

  ΣToNaturalP : {A B : PresentedSimplicialSet ℓ}
              → NaturalΣP A B → PresentedNatural A B
  mapPCell (ΣToNaturalP (f , p)) = f
  face-naturalP (ΣToNaturalP (f , p)) {n} = fst p n
  degen-naturalP (ΣToNaturalP (f , p)) {n} = snd p n

isSetPresentedNatural : {A B : PresentedSimplicialSet ℓ}
                      → isSet (PresentedNatural A B)
isSetPresentedNatural {A = A} {B = B} =
  isSetRetract naturalToΣP ΣToNaturalP
    (λ f → presentedNaturalExt (λ _ _ → refl))
    (isSetΣSndProp (isSetΠ2 λ n _ → snd (cellsP B n))
      (naturalProofP-isProp A B))

presented-left-id : {A B : PresentedSimplicialSet ℓ} (f : PresentedNatural A B)
                  → presentedCompose (presentedIdentity A) f ≡ f
presented-left-id f = presentedNaturalExt (λ _ _ → refl)

presented-right-id : {A B : PresentedSimplicialSet ℓ} (f : PresentedNatural A B)
                   → presentedCompose f (presentedIdentity B) ≡ f
presented-right-id f = presentedNaturalExt (λ _ _ → refl)

presented-associativity : {A B C D : PresentedSimplicialSet ℓ}
                         (f : PresentedNatural A B) (g : PresentedNatural B C)
                         (h : PresentedNatural C D)
                       → presentedCompose (presentedCompose f g) h
                       ≡ presentedCompose f (presentedCompose g h)
presented-associativity f g h = presentedNaturalExt (λ _ _ → refl)

PresentedSimplicialSetCategory : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (PresentedSimplicialSetCategory ℓ) = PresentedSimplicialSet ℓ
Category.Hom[_,_] (PresentedSimplicialSetCategory ℓ) = PresentedNatural
Category.id (PresentedSimplicialSetCategory ℓ) {x = A} = presentedIdentity A
Category._⋆_ (PresentedSimplicialSetCategory ℓ) = presentedCompose
Category.⋆IdL (PresentedSimplicialSetCategory ℓ) = presented-left-id
Category.⋆IdR (PresentedSimplicialSetCategory ℓ) = presented-right-id
Category.⋆Assoc (PresentedSimplicialSetCategory ℓ) = presented-associativity
Category.isSetHom (PresentedSimplicialSetCategory ℓ) = isSetPresentedNatural
