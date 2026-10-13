{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.PresentedProducts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit*; tt*; isSetUnit*; isPropUnit*)
open import Cubical.Categories.Limits.BinProduct using (BinProduct)
open import Cubical.Categories.Limits.Terminal using (Terminal)
open import DHH.Simplicial.Presented
open import DHH.Simplicial.PresentedCategory

private variable ℓ : Level

-- Products and the terminal object are defined degreewise.  This is a
-- construction on the presented simplex category; it needs no claim
-- that its evaluation into the concrete ordinal category is faithful.
presentedTerminal : (ℓ : Level) → PresentedSimplicialSet ℓ
cellsP (presentedTerminal ℓ) n = Unit* , isSetUnit*
faceP (presentedTerminal ℓ) i c = c
degenP (presentedTerminal ℓ) i c = c
facesP (presentedTerminal ℓ) p c = refl
degensP (presentedTerminal ℓ) p c = refl
sameP (presentedTerminal ℓ) i c = refl
nextP (presentedTerminal ℓ) i c = refl
beforeP (presentedTerminal ℓ) p c = refl
afterP (presentedTerminal ℓ) p c = refl

terminalMap : (A : PresentedSimplicialSet ℓ) → PresentedNatural A (presentedTerminal ℓ)
mapPCell (terminalMap A) n c = tt*
face-naturalP (terminalMap A) i c = refl
degen-naturalP (terminalMap A) i c = refl

terminalMap-unique : {A : PresentedSimplicialSet ℓ}
                    (f : PresentedNatural A (presentedTerminal ℓ))
                  → terminalMap A ≡ f
terminalMap-unique f = presentedNaturalExt (λ _ _ → isPropUnit* _ _)

presentedTerminalObject : (ℓ : Level) → Terminal (PresentedSimplicialSetCategory ℓ)
presentedTerminalObject ℓ = presentedTerminal ℓ , λ A → terminalMap A , terminalMap-unique

presentedProduct : PresentedSimplicialSet ℓ → PresentedSimplicialSet ℓ
                 → PresentedSimplicialSet ℓ
cellsP (presentedProduct A B) n =
  (PCell A n × PCell B n) , isSet× (snd (cellsP A n)) (snd (cellsP B n))
faceP (presentedProduct A B) i (a , b) = faceP A i a , faceP B i b
degenP (presentedProduct A B) i (a , b) = degenP A i a , degenP B i b
facesP (presentedProduct A B) p (a , b) j = facesP A p a j , facesP B p b j
degensP (presentedProduct A B) p (a , b) j = degensP A p a j , degensP B p b j
sameP (presentedProduct A B) i (a , b) j = sameP A i a j , sameP B i b j
nextP (presentedProduct A B) i (a , b) j = nextP A i a j , nextP B i b j
beforeP (presentedProduct A B) p (a , b) j = beforeP A p a j , beforeP B p b j
afterP (presentedProduct A B) p (a , b) j = afterP A p a j , afterP B p b j

firstProjection : {A B : PresentedSimplicialSet ℓ}
                 → PresentedNatural (presentedProduct A B) A
mapPCell firstProjection n c = fst c
face-naturalP firstProjection i c = refl
degen-naturalP firstProjection i c = refl

secondProjection : {A B : PresentedSimplicialSet ℓ}
                  → PresentedNatural (presentedProduct A B) B
mapPCell secondProjection n c = snd c
face-naturalP secondProjection i c = refl
degen-naturalP secondProjection i c = refl

presentedPairing : {A B C : PresentedSimplicialSet ℓ}
                 → PresentedNatural A B → PresentedNatural A C
                 → PresentedNatural A (presentedProduct B C)
mapPCell (presentedPairing f g) n c = mapPCell f n c , mapPCell g n c
face-naturalP (presentedPairing f g) i c j = face-naturalP f i c j , face-naturalP g i c j
degen-naturalP (presentedPairing f g) i c j = degen-naturalP f i c j , degen-naturalP g i c j

pairing-first : {A B C : PresentedSimplicialSet ℓ}
                (f : PresentedNatural A B) (g : PresentedNatural A C)
              → presentedCompose (presentedPairing f g) (firstProjection {A = B} {B = C}) ≡ f
pairing-first f g = presentedNaturalExt (λ _ _ → refl)

pairing-second : {A B C : PresentedSimplicialSet ℓ}
                 (f : PresentedNatural A B) (g : PresentedNatural A C)
               → presentedCompose (presentedPairing f g) (secondProjection {A = B} {B = C}) ≡ g
pairing-second f g = presentedNaturalExt (λ _ _ → refl)

pairing-unique : {A B C : PresentedSimplicialSet ℓ}
                 (f : PresentedNatural A B) (g : PresentedNatural A C)
                 (h : PresentedNatural A (presentedProduct B C))
               → presentedCompose h (firstProjection {A = B} {B = C}) ≡ f
               → presentedCompose h (secondProjection {A = B} {B = C}) ≡ g
               → presentedPairing f g ≡ h
pairing-unique f g h p q = presentedNaturalExt λ n c j →
  mapPCell (sym p j) n c , mapPCell (sym q j) n c

pairing-eta : {A B C : PresentedSimplicialSet ℓ}
              (h : PresentedNatural A (presentedProduct B C))
            → presentedPairing (presentedCompose h (firstProjection {A = B} {B = C}))
                (presentedCompose h (secondProjection {A = B} {B = C})) ≡ h
pairing-eta h = presentedNaturalExt (λ _ _ → refl)

-- The categorical universal property includes existence and uniqueness
-- of the factorization, not merely a chosen pair of projection maps.
presentedBinProduct : (A B : PresentedSimplicialSet ℓ)
                    → BinProduct (PresentedSimplicialSetCategory ℓ) A B
BinProduct.binProdOb (presentedBinProduct A B) = presentedProduct A B
BinProduct.binProdPr₁ (presentedBinProduct A B) = firstProjection {A = A} {B = B}
BinProduct.binProdPr₂ (presentedBinProduct A B) = secondProjection {A = A} {B = B}
BinProduct.univProp (presentedBinProduct A B) f g =
  (presentedPairing f g , pairing-first f g , pairing-second f g) ,
  λ { (h , p , q) →
    Σ≡Prop (λ _ → isProp× (isSetPresentedNatural _ _) (isSetPresentedNatural _ _))
      (pairing-unique f g h p q) }

productMap : {A B C D : PresentedSimplicialSet ℓ}
            → PresentedNatural A B → PresentedNatural C D
            → PresentedNatural (presentedProduct A C) (presentedProduct B D)
productMap {A = A} {C = C} f g = presentedPairing
  (presentedCompose (firstProjection {A = A} {B = C}) f)
  (presentedCompose (secondProjection {A = A} {B = C}) g)

productMap-id : (A B : PresentedSimplicialSet ℓ)
              → productMap (presentedIdentity A) (presentedIdentity B)
              ≡ presentedIdentity (presentedProduct A B)
productMap-id A B = presentedNaturalExt (λ _ _ → refl)

productMap-compose : {A B C D E F : PresentedSimplicialSet ℓ}
                      (f : PresentedNatural A B) (g : PresentedNatural B C)
                      (h : PresentedNatural D E) (k : PresentedNatural E F)
                    → productMap (presentedCompose f g) (presentedCompose h k)
                    ≡ presentedCompose (productMap f h) (productMap g k)
productMap-compose f g h k = presentedNaturalExt (λ _ _ → refl)
