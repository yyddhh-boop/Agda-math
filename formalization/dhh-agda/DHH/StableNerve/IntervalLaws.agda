{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntervalLaws where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import DHH.StableNerve.Interval

min-zeroR : {m : ℕ} (x : Fin (suc m)) → minFin x fzero ≡ fzero
min-zeroR fzero = refl
min-zeroR (fsuc x) = refl
max-zeroR : {m : ℕ} (x : Fin (suc m)) → maxFin x fzero ≡ x
max-zeroR fzero = refl
max-zeroR (fsuc x) = refl

left-endpoint : (m : ℕ) (b : Bool) → leftCollapse (endpoint (suc m) b) ≡ endpoint m b
left-endpoint m false = refl
left-endpoint m true = refl
right-endpoint : (m : ℕ) (b : Bool) → rightCollapse (endpoint (suc m) b) ≡ endpoint m b
right-endpoint m false = refl
right-endpoint zero true = refl
right-endpoint (suc m) true = cong fsuc (right-endpoint m true)

left-min : {m : ℕ} (x y : Fin (suc (suc m)))
  → leftCollapse (minFin x y) ≡ minFin (leftCollapse x) (leftCollapse y)
left-min fzero y = refl
left-min (fsuc x) fzero = sym (min-zeroR x)
left-min (fsuc x) (fsuc y) = refl
left-max : {m : ℕ} (x y : Fin (suc (suc m)))
  → leftCollapse (maxFin x y) ≡ maxFin (leftCollapse x) (leftCollapse y)
left-max fzero y = refl
left-max (fsuc x) fzero = sym (max-zeroR x)
left-max (fsuc x) (fsuc y) = refl

right-min : {m : ℕ} (x y : Fin (suc (suc m)))
  → rightCollapse (minFin x y) ≡ minFin (rightCollapse x) (rightCollapse y)
right-min fzero y = refl
right-min {zero} (fsuc x) fzero = refl
right-min {zero} (fsuc x) (fsuc y) = refl
right-min {suc m} (fsuc x) fzero = refl
right-min {suc m} (fsuc x) (fsuc y) = cong fsuc (right-min x y)
right-max : {m : ℕ} (x y : Fin (suc (suc m)))
  → rightCollapse (maxFin x y) ≡ maxFin (rightCollapse x) (rightCollapse y)
right-max fzero y = refl
right-max {zero} (fsuc x) fzero = refl
right-max {zero} (fsuc x) (fsuc y) = refl
right-max {suc m} (fsuc x) fzero = refl
right-max {suc m} (fsuc x) (fsuc y) = cong fsuc (right-max x y)

-- Both-end extensions commute, exactly as CK's c = l r = r l.
left-right : {m : ℕ} (x : Fin (suc (suc (suc m))))
  → leftCollapse (rightCollapse x) ≡ rightCollapse (leftCollapse x)
left-right fzero = refl
left-right (fsuc x) = refl
