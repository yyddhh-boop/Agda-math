{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.OrdinalCuts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Unit using (tt)
open import DHH.Simplicial.Ordinal

-- A monotone binary labeling of [n] is a cut: a string of zeroes
-- followed by a string of ones, including both constant strings.
-- Precomposition gives the contravariant action without choosing a
-- factorization into elementary simplex maps.
Cut : ℕ → Type₀
Cut n = OrdinalMap n 1

cutZero cutOne : (n : ℕ) → Cut n
mapIndex (cutZero n) i = fzero
monotone (cutZero n) i j p = tt
mapIndex (cutOne n) i = fsuc fzero
monotone (cutOne n) i j p = tt

CutLe : {n : ℕ} → Cut n → Cut n → Type₀
CutLe c d = ∀ i → mapIndex c i ≤F mapIndex d i

cutLe-isProp : {n : ℕ} (c d : Cut n) → isProp (CutLe c d)
cutLe-isProp c d = isPropΠ (λ i → ≤F-isProp (mapIndex c i) (mapIndex d i))

pullCut : {m n : ℕ} → OrdinalMap m n → Cut n → Cut m
pullCut f c = f ⋆o c

pullCut-monotone : {m n : ℕ} (f : OrdinalMap m n) {c d : Cut n}
  → CutLe c d → CutLe (pullCut f c) (pullCut f d)
pullCut-monotone f e i = e (mapIndex f i)

pullCut-zero : {m n : ℕ} (f : OrdinalMap m n) → pullCut f (cutZero n) ≡ cutZero m
pullCut-zero f = ordinalMapExt (λ _ → refl)

pullCut-one : {m n : ℕ} (f : OrdinalMap m n) → pullCut f (cutOne n) ≡ cutOne m
pullCut-one f = ordinalMapExt (λ _ → refl)

pullCut-id : {n : ℕ} (c : Cut n) → pullCut (ordinalId n) c ≡ c
pullCut-id c = ordinalMapExt (λ _ → refl)

pullCut-compose : {l m n : ℕ} (f : OrdinalMap l m) (g : OrdinalMap m n) (c : Cut n)
  → pullCut (f ⋆o g) c ≡ pullCut f (pullCut g c)
pullCut-compose f g c = ordinalMapExt (λ _ → refl)
