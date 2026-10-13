{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.CutClassification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; weakenFin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ; _,_)
import Cubical.Data.Empty as Empty
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Word using (tailOrdinal; revealIndex; singletonIndex; nonzeroEverywhere)
open import DHH.Simplicial.OrdinalCuts

lastFin : (n : ℕ) → Fin (suc n)
lastFin zero = fzero
lastFin (suc n) = fsuc (lastFin n)

shiftSplit : {n : ℕ} → Fin n ⊎ Unit → Fin (suc n) ⊎ Unit
shiftSplit (inl j) = inl (fsuc j)
shiftSplit (inr tt) = inr tt

splitLast : {n : ℕ} → Fin (suc n) → Fin n ⊎ Unit
splitLast {n = zero} fzero = inr tt
splitLast {n = suc n} fzero = inl fzero
splitLast {n = suc n} (fsuc i) = shiftSplit (splitLast i)

joinLast : {n : ℕ} → Fin n ⊎ Unit → Fin (suc n)
joinLast (inl i) = weakenFin i
joinLast {n = n} (inr tt) = lastFin n

split-weaken : {n : ℕ} (i : Fin n) → splitLast (weakenFin i) ≡ inl i
split-weaken {n = suc n} fzero = refl
split-weaken {n = suc n} (fsuc i) = cong shiftSplit (split-weaken i)

split-last : (n : ℕ) → splitLast (lastFin n) ≡ inr tt
split-last zero = refl
split-last (suc n) = cong shiftSplit (split-last n)

join-split : {n : ℕ} (i : Fin (suc n)) → joinLast (splitLast i) ≡ i
join-split {n = zero} fzero = refl
join-split {n = suc n} fzero = refl
join-split {n = suc n} (fsuc i) with splitLast i | join-split i
... | inl j | p = cong fsuc p
... | inr tt | p = cong fsuc p

revealSplit : {n : ℕ} (i : Fin (suc n))
  → Σ (Fin n ⊎ Unit) (λ s → splitLast i ≡ s)
revealSplit i = splitLast i , refl

prependZero : {n : ℕ} → Cut n → Cut (suc n)
mapIndex (prependZero c) fzero = fzero
mapIndex (prependZero c) (fsuc i) = mapIndex c i
monotone (prependZero c) fzero j p = tt
monotone (prependZero c) (fsuc i) fzero ()
monotone (prependZero c) (fsuc i) (fsuc j) p = monotone c i j p

head-zero-reconstruct : {n : ℕ} (c : Cut (suc n))
  → mapIndex c fzero ≡ fzero → prependZero (tailOrdinal c) ≡ c
head-zero-reconstruct c e = ordinalMapExt λ where
  fzero → sym e
  (fsuc i) → refl

oneIndex : Fin 2
oneIndex = fsuc fzero

one-is-max : (b : Fin 2) → oneIndex ≤F b → b ≡ oneIndex
one-is-max fzero ()
one-is-max (fsuc fzero) p = refl
one-is-max (fsuc (fsuc ())) p

head-one-all : {n : ℕ} (c : Cut n)
  → mapIndex c fzero ≡ fsuc fzero → (i : Fin (suc n)) → mapIndex c i ≡ fsuc fzero
head-one-all c e i = one-is-max (mapIndex c i) (nonzeroEverywhere c fzero e i)

head-one-reconstruct : {n : ℕ} (c : Cut n)
  → mapIndex c fzero ≡ fsuc fzero → cutOne n ≡ c
head-one-reconstruct c e = ordinalMapExt (λ i → sym (head-one-all c e i))

encodeCut : (n : ℕ) → Cut n → Fin (suc (suc n))
encodeCut zero c = mapIndex c fzero
encodeCut (suc n) c with revealIndex c fzero
... | fzero , e = weakenFin (encodeCut n (tailOrdinal c))
... | fsuc fzero , e = lastFin (suc (suc n))
... | fsuc (fsuc ()) , e

mutual
  decodeCut : (n : ℕ) → Fin (suc (suc n)) → Cut n
  mapIndex (decodeCut zero k) i = k
  monotone (decodeCut zero k) i j p = ≤F-refl k
  decodeCut (suc n) k = decodeSplit n (splitLast k)

  decodeSplit : (n : ℕ) → Fin (suc (suc n)) ⊎ Unit → Cut (suc n)
  decodeSplit n (inl k) = prependZero (decodeCut n k)
  decodeSplit n (inr tt) = cutOne (suc n)

decode-weaken : (n : ℕ) (k : Fin (suc (suc n)))
  → decodeCut (suc n) (weakenFin k) ≡ prependZero (decodeCut n k)
decode-weaken n k = cong (decodeSplit n) (split-weaken k)

decode-last : (n : ℕ)
  → decodeCut (suc n) (lastFin (suc (suc n))) ≡ cutOne (suc n)
decode-last n = cong (decodeSplit n) (split-last (suc (suc n)))

encode-prepend : (n : ℕ) (c : Cut n)
  → encodeCut (suc n) (prependZero c) ≡ weakenFin (encodeCut n c)
encode-prepend n c = refl

encode-zero : (n : ℕ) → encodeCut n (cutZero n) ≡ fzero
encode-zero zero = refl
encode-zero (suc n) = cong weakenFin (encode-zero n)

encode-one : (n : ℕ) → encodeCut n (cutOne n) ≡ lastFin (suc n)
encode-one zero = refl
encode-one (suc n) = refl

decode-encode : (n : ℕ) (c : Cut n) → decodeCut n (encodeCut n c) ≡ c
decode-encode zero c = ordinalMapExt (λ i → cong (mapIndex c) (sym (singletonIndex i)))
decode-encode (suc n) c with revealIndex c fzero
... | fzero , e = decode-weaken n (encodeCut n (tailOrdinal c))
  ∙ cong prependZero (decode-encode n (tailOrdinal c)) ∙ head-zero-reconstruct c e
... | fsuc fzero , e = decode-last n ∙ head-one-reconstruct c e
... | fsuc (fsuc ()) , e

encode-decode : (n : ℕ) (k : Fin (suc (suc n))) → encodeCut n (decodeCut n k) ≡ k
encode-decode zero k = refl
encode-decode (suc n) k with revealSplit k
... | inl j , e = cong (λ s → encodeCut (suc n) (decodeSplit n s)) e
  ∙ encode-prepend n (decodeCut n j) ∙ cong weakenFin (encode-decode n j)
  ∙ sym (cong joinLast e) ∙ join-split k
... | inr tt , e = cong (λ s → encodeCut (suc n) (decodeSplit n s)) e
  ∙ encode-one (suc n) ∙ sym (cong joinLast e) ∙ join-split k

cutClassificationIso : (n : ℕ) → Iso (Cut n) (Fin (suc (suc n)))
Iso.fun (cutClassificationIso n) = encodeCut n
Iso.inv (cutClassificationIso n) = decodeCut n
Iso.rightInv (cutClassificationIso n) = encode-decode n
Iso.leftInv (cutClassificationIso n) = decode-encode n

cutClassificationEquivalence : (n : ℕ) → Cut n ≃ Fin (suc (suc n))
cutClassificationEquivalence n = isoToEquiv (cutClassificationIso n)

weaken-order : {n : ℕ} {i j : Fin n}
  → i ≤F j → weakenFin i ≤F weakenFin j
weaken-order {i = fzero} {j = j} p = tt
weaken-order {i = fsuc i} {j = fzero} ()
weaken-order {i = fsuc i} {j = fsuc j} p = weaken-order {i = i} {j = j} p

unweaken-order : {n : ℕ} {i j : Fin n}
  → weakenFin i ≤F weakenFin j → i ≤F j
unweaken-order {i = fzero} {j = j} p = tt
unweaken-order {i = fsuc i} {j = fzero} ()
unweaken-order {i = fsuc i} {j = fsuc j} p = unweaken-order {i = i} {j = j} p

below-last : {n : ℕ} (i : Fin (suc n)) → i ≤F lastFin n
below-last fzero = tt
below-last {n = suc n} (fsuc i) = below-last i

last-not-below-weaken : {n : ℕ} (i : Fin n) → lastFin n ≤F weakenFin i → Empty.⊥
last-not-below-weaken {n = suc n} fzero ()
last-not-below-weaken {n = suc n} (fsuc i) p = last-not-below-weaken i p

bool-below-one : (b : Fin 2) → b ≤F oneIndex
bool-below-one fzero = tt
bool-below-one (fsuc fzero) = tt
bool-below-one (fsuc (fsuc ()))

order-to-one : {n : ℕ} (c d : Cut n) → mapIndex d fzero ≡ fsuc fzero → CutLe c d
order-to-one c d e i = subst ((mapIndex c i) ≤F_)
  (sym (head-one-all d e i)) (bool-below-one (mapIndex c i))

encodeCut-monotone : (n : ℕ) {c d : Cut n}
  → CutLe c d → encodeCut n c ≤F encodeCut n d
encodeCut-monotone zero p = p fzero
encodeCut-monotone (suc n) {c} {d} p with revealIndex c fzero | revealIndex d fzero
... | fzero , e | fzero , f = weaken-order {i = encodeCut n (tailOrdinal c)} {j = encodeCut n (tailOrdinal d)}
  (encodeCut-monotone n {c = tailOrdinal c} {d = tailOrdinal d} (λ i → p (fsuc i)))
... | fzero , e | fsuc fzero , f = below-last (weakenFin (encodeCut n (tailOrdinal c)))
... | fsuc fzero , e | fsuc fzero , f = ≤F-refl (lastFin (suc (suc n)))
... | fsuc fzero , e | fzero , f = Empty.rec (subst2 _≤F_ e f (p fzero))
... | fsuc (fsuc ()) , e | b , f
... | b , e | fsuc (fsuc ()) , f

encodeCut-reflects-order : (n : ℕ) {c d : Cut n}
  → encodeCut n c ≤F encodeCut n d → CutLe c d
encodeCut-reflects-order zero {c} {d} p i = subst2 _≤F_
  (cong (mapIndex c) (sym (singletonIndex i)))
  (cong (mapIndex d) (sym (singletonIndex i))) p
encodeCut-reflects-order (suc n) {c} {d} p with revealIndex c fzero | revealIndex d fzero
... | fzero , e | fzero , f = λ where
  fzero → subst2 _≤F_ (sym e) (sym f) tt
  (fsuc i) → encodeCut-reflects-order n {c = tailOrdinal c} {d = tailOrdinal d}
    (unweaken-order {i = encodeCut n (tailOrdinal c)} {j = encodeCut n (tailOrdinal d)} p) i
... | fzero , e | fsuc fzero , f = order-to-one c d f
... | fsuc fzero , e | fsuc fzero , f = order-to-one c d f
... | fsuc fzero , e | fzero , f = Empty.rec (last-not-below-weaken (encodeCut n (tailOrdinal d)) p)
... | fsuc (fsuc ()) , e | b , f
... | b , e | fsuc (fsuc ()) , f

-- Convenient consequences for reindexing interval coordinates.
decode-zero : (n : ℕ) → decodeCut n fzero ≡ cutZero n
decode-zero n = cong (decodeCut n) (sym (encode-zero n)) ∙ decode-encode n (cutZero n)

decode-one : (n : ℕ) → decodeCut n (lastFin (suc n)) ≡ cutOne n
decode-one n = cong (decodeCut n) (sym (encode-one n)) ∙ decode-encode n (cutOne n)

decodeCut-monotone : (n : ℕ) {i j : Fin (suc (suc n))}
  → i ≤F j → CutLe (decodeCut n i) (decodeCut n j)
decodeCut-monotone n {i} {j} p = encodeCut-reflects-order n
  {c = decodeCut n i} {d = decodeCut n j}
  (subst2 _≤F_ (sym (encode-decode n i)) (sym (encode-decode n j)) p)

cutOrderIso : (n : ℕ) (c d : Cut n)
  → Iso (CutLe c d) (encodeCut n c ≤F encodeCut n d)
Iso.fun (cutOrderIso n c d) = encodeCut-monotone n {c = c} {d = d}
Iso.inv (cutOrderIso n c d) = encodeCut-reflects-order n {c = c} {d = d}
Iso.rightInv (cutOrderIso n c d) p = ≤F-isProp (encodeCut n c) (encodeCut n d) _ p
Iso.leftInv (cutOrderIso n c d) p = cutLe-isProp c d _ p

cutOrderEquivalence : (n : ℕ) (c d : Cut n)
  → CutLe c d ≃ (encodeCut n c ≤F encodeCut n d)
cutOrderEquivalence n c d = isoToEquiv (cutOrderIso n c d)
