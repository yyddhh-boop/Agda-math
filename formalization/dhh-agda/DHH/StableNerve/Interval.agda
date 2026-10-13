{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; isSetFin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true; true≢false; false≢true)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import DHH.Graph
open import DHH.Cubes using (meetBool; joinBool)

IsZero : {m : ℕ} → Fin (suc m) → Type₀
IsZero fzero = Unit
IsZero (fsuc x) = ⊥

Near : {m : ℕ} → Fin (suc m) → Fin (suc m) → Type₀
Near fzero fzero = Unit
Near {suc m} fzero (fsuc y) = IsZero y
Near {suc m} (fsuc x) fzero = IsZero x
Near {suc m} (fsuc x) (fsuc y) = Near x y

near-prop : {m : ℕ} (x y : Fin (suc m)) → isProp (Near x y)
near-prop fzero fzero = isPropUnit
near-prop {suc m} fzero (fsuc fzero) = isPropUnit
near-prop {suc m} fzero (fsuc (fsuc y)) = isProp⊥
near-prop {suc m} (fsuc fzero) fzero = isPropUnit
near-prop {suc m} (fsuc (fsuc x)) fzero = isProp⊥
near-prop {suc m} (fsuc x) (fsuc y) = near-prop x y

near-refl : {m : ℕ} (x : Fin (suc m)) → Near x x
near-refl fzero = tt
near-refl {suc m} (fsuc x) = near-refl x

near-sym : {m : ℕ} {x y : Fin (suc m)} → Near x y → Near y x
near-sym {x = fzero} {fzero} e = e
near-sym {suc m} {fzero} {fsuc y} e = e
near-sym {suc m} {fsuc x} {fzero} e = e
near-sym {suc m} {fsuc x} {fsuc y} e = near-sym {m} {x} {y} e

Iₘ : ℕ → Graph ℓ-zero
Vertex (Iₘ m) = Fin (suc m)
vertex-isSet (Iₘ m) = isSetFin
Adj (Iₘ m) = Near
adj-isProp (Iₘ m) = near-prop
adj-refl (Iₘ m) = near-refl
adj-sym (Iₘ m) {x = x} {y = y} = near-sym {m} {x} {y}

top : (m : ℕ) → Fin (suc m)
top zero = fzero
top (suc m) = fsuc (top m)

endpoint : (m : ℕ) → Bool → Fin (suc m)
endpoint m false = fzero
endpoint m true = top m

leftCollapse : {m : ℕ} → Fin (suc (suc m)) → Fin (suc m)
leftCollapse fzero = fzero
leftCollapse (fsuc x) = x

rightCollapse : {m : ℕ} → Fin (suc (suc m)) → Fin (suc m)
rightCollapse fzero = fzero
rightCollapse {zero} (fsuc x) = fzero
rightCollapse {suc m} (fsuc x) = fsuc (rightCollapse x)

left-near : {m : ℕ} {x y : Fin (suc (suc m))} → Near x y → Near (leftCollapse x) (leftCollapse y)
left-near {x = fzero} {fzero} e = tt
left-near {x = fzero} {fsuc fzero} e = tt
left-near {x = fzero} {fsuc (fsuc y)} ()
left-near {x = fsuc fzero} {fzero} e = tt
left-near {x = fsuc (fsuc x)} {fzero} ()
left-near {x = fsuc x} {fsuc y} e = e

right-near : {m : ℕ} {x y : Fin (suc (suc m))} → Near x y → Near (rightCollapse x) (rightCollapse y)
right-near {zero} {fzero} {fzero} e = tt
right-near {zero} {fzero} {fsuc y} e = tt
right-near {zero} {fsuc x} {fzero} e = tt
right-near {zero} {fsuc x} {fsuc y} e = tt
right-near {suc m} {fzero} {fzero} e = tt
right-near {suc m} {fzero} {fsuc fzero} e = tt
right-near {suc m} {fzero} {fsuc (fsuc y)} ()
right-near {suc m} {fsuc fzero} {fzero} e = tt
right-near {suc m} {fsuc (fsuc x)} {fzero} ()
right-near {suc m} {fsuc x} {fsuc y} e = right-near {m} {x} {y} e

leftMap : (m : ℕ) → Hom (Iₘ (suc m)) (Iₘ m)
onVertices (leftMap m) = leftCollapse
preserves (leftMap m) {x = x} {y = y} = left-near {m} {x} {y}
rightMap : (m : ℕ) → Hom (Iₘ (suc m)) (Iₘ m)
onVertices (rightMap m) = rightCollapse
preserves (rightMap m) {x = x} {y = y} = right-near {m} {x} {y}

minFin maxFin : {m : ℕ} → Fin (suc m) → Fin (suc m) → Fin (suc m)
minFin fzero y = fzero
minFin (fsuc x) fzero = fzero
minFin {suc m} (fsuc x) (fsuc y) = fsuc (minFin x y)
maxFin fzero y = y
maxFin (fsuc x) fzero = fsuc x
maxFin {suc m} (fsuc x) (fsuc y) = fsuc (maxFin x y)

min-comm : {m : ℕ} (x y : Fin (suc m)) → minFin x y ≡ minFin y x
min-comm fzero fzero = refl
min-comm fzero (fsuc y) = refl
min-comm (fsuc x) fzero = refl
min-comm {suc m} (fsuc x) (fsuc y) = cong fsuc (min-comm x y)
max-commutative : {m : ℕ} (x y : Fin (suc m)) → maxFin x y ≡ maxFin y x
max-commutative fzero fzero = refl
max-commutative fzero (fsuc y) = refl
max-commutative (fsuc x) fzero = refl
max-commutative {suc m} (fsuc x) (fsuc y) = cong fsuc (max-commutative x y)

min-near-left : {m : ℕ} {x y : Fin (suc m)} → Near x y → (z : Fin (suc m)) → Near (minFin x z) (minFin y z)
min-near-left {x = fzero} {fzero} e fzero = tt
min-near-left {x = fzero} {fsuc y} e fzero = tt
min-near-left {x = fsuc x} {fzero} e fzero = tt
min-near-left {x = fsuc x} {fsuc y} e fzero = tt
min-near-left {suc m} {fzero} {fzero} e (fsuc z) = tt
min-near-left {suc m} {fzero} {fsuc fzero} e (fsuc z) = tt
min-near-left {suc m} {fzero} {fsuc (fsuc y)} () (fsuc z)
min-near-left {suc m} {fsuc fzero} {fzero} e (fsuc z) = tt
min-near-left {suc m} {fsuc (fsuc x)} {fzero} () (fsuc z)
min-near-left {suc m} {fsuc x} {fsuc y} e (fsuc z) = min-near-left {m} {x} {y} e z

max-near-left : {m : ℕ} {x y : Fin (suc m)} → Near x y → (z : Fin (suc m)) → Near (maxFin x z) (maxFin y z)
max-near-left {x = fzero} {fzero} e fzero = tt
max-near-left {x = fzero} {fsuc y} e fzero = e
max-near-left {x = fsuc x} {fzero} e fzero = e
max-near-left {suc m} {fsuc x} {fsuc y} e fzero = e
max-near-left {suc m} {fzero} {fzero} e (fsuc z) = near-refl z
max-near-left {suc m} {fzero} {fsuc fzero} e (fsuc z) = near-refl z
max-near-left {suc m} {fzero} {fsuc (fsuc y)} () (fsuc z)
max-near-left {suc m} {fsuc fzero} {fzero} e (fsuc z) = near-refl z
max-near-left {suc m} {fsuc (fsuc x)} {fzero} () (fsuc z)
max-near-left {suc m} {fsuc x} {fsuc y} e (fsuc z) = max-near-left {m} {x} {y} e z

min-near-right : {m : ℕ} (z : Fin (suc m)) {x y : Fin (suc m)} → Near x y → Near (minFin z x) (minFin z y)
min-near-right {m} z {x} {y} e = subst2 (Near {m}) (min-comm x z) (min-comm y z) (min-near-left {m} {x} {y} e z)
max-near-right : {m : ℕ} (z : Fin (suc m)) {x y : Fin (suc m)} → Near x y → Near (maxFin z x) (maxFin z y)
max-near-right {m} z {x} {y} e = subst2 (Near {m}) (max-commutative x z) (max-commutative y z) (max-near-left {m} {x} {y} e z)

-- Positive thresholds 1,...,m, encoded by Fin m.
threshold : {m : ℕ} → Fin m → Fin (suc m) → Bool
threshold t fzero = false
threshold fzero (fsuc x) = true
threshold {suc m} (fsuc t) (fsuc x) = threshold t x

threshold-top : {m : ℕ} (t : Fin m) → threshold t (top m) ≡ true
threshold-top {suc m} fzero = refl
threshold-top {suc m} (fsuc t) = threshold-top t

threshold-endpoint : {m : ℕ} (t : Fin m) (b : Bool) → threshold t (endpoint m b) ≡ b
threshold-endpoint t false = refl
threshold-endpoint t true = threshold-top t

threshold-min : {m : ℕ} (t : Fin m) (x y : Fin (suc m))
  → threshold t (minFin x y) ≡ meetBool (threshold t x) (threshold t y)
threshold-min t fzero y = refl
threshold-min t (fsuc x) fzero with threshold t (fsuc x)
... | false = refl
... | true = refl
threshold-min {suc m} fzero (fsuc x) (fsuc y) = refl
threshold-min {suc m} (fsuc t) (fsuc x) (fsuc y) = threshold-min t x y

threshold-max : {m : ℕ} (t : Fin m) (x y : Fin (suc m))
  → threshold t (maxFin x y) ≡ joinBool (threshold t x) (threshold t y)
threshold-max t fzero y = refl
threshold-max t (fsuc x) fzero with threshold t (fsuc x)
... | false = refl
... | true = refl
threshold-max {suc m} fzero (fsuc x) (fsuc y) = refl
threshold-max {suc m} (fsuc t) (fsuc x) (fsuc y) = threshold-max t x y

threshold-ext : {m : ℕ} (x y : Fin (suc m))
  → ((t : Fin m) → threshold t x ≡ threshold t y) → x ≡ y
threshold-ext fzero fzero p = refl
threshold-ext {suc m} fzero (fsuc y) p = Cubical.Data.Empty.rec (false≢true (p fzero))
threshold-ext {suc m} (fsuc x) fzero p = Cubical.Data.Empty.rec (true≢false (p fzero))
threshold-ext {suc m} (fsuc x) (fsuc y) p = cong fsuc (threshold-ext x y (λ t → p (fsuc t)))
