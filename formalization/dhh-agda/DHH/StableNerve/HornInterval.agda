{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornInterval where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_≤_; pred-≤-pred)
open import Cubical.Data.FinData using (Fin; toℕ; toℕ<n)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Unit using (tt)
open import DHH.Graph
open import DHH.StableNerve.Interval
open import DHH.StableNerve.IntegerClamp using (clampNat; clamp-inclusion)
open import DHH.StableNerve.HornScalar

-- 把纯自然数的递归程序接到实际有限区间图。NearNat 和 Near
-- 的证明按共同后继剥离；没有生成一个大小依赖 m 的邻接表。
finite-near-nat : {m : ℕ} {x y : Fin (suc m)}
  → Near x y → NearNat (toℕ x) (toℕ y)
finite-near-nat {x = fzero} {fzero} e = tt
finite-near-nat {suc m} {fzero} {fsuc fzero} e = tt
finite-near-nat {suc m} {fzero} {fsuc (fsuc y)} ()
finite-near-nat {suc m} {fsuc fzero} {fzero} e = tt
finite-near-nat {suc m} {fsuc (fsuc x)} {fzero} ()
finite-near-nat {suc m} {fsuc x} {fsuc y} e = finite-near-nat {m} {x} {y} e

clampNat-zero : (k : ℕ) → clampNat zero k ≡ fzero
clampNat-zero zero = refl
clampNat-zero (suc k) = refl

clampNat-near : (m : ℕ) {x y : ℕ} → NearNat x y
  → Near (clampNat m x) (clampNat m y)
clampNat-near zero {x} {y} e =
  subst2 (Near {zero}) (sym (clampNat-zero x)) (sym (clampNat-zero y)) tt
clampNat-near (suc m) {zero} {zero} e = tt
clampNat-near (suc m) {zero} {suc zero} e = tt
clampNat-near (suc m) {zero} {suc (suc y)} ()
clampNat-near (suc m) {suc zero} {zero} e = tt
clampNat-near (suc m) {suc (suc x)} {zero} ()
clampNat-near (suc m) {suc x} {suc y} e = clampNat-near m {x} {y} e

finite-bound : {m : ℕ} (x : Fin (suc m)) → toℕ x ≤ m
finite-bound x = pred-≤-pred (toℕ<n x)

-- D 固定时，两种缺面方向均给实际保边图同态。
-- 这里不包装为 IntervalMorph：它们通常不同时固定两个端点。
positiveMap negativeMap : (m D : ℕ) → Hom (Iₘ m) (Iₘ m)
onVertices (positiveMap m D) x = clampNat m (positiveHeight m D (toℕ x))
preserves (positiveMap m D) {x} {y} e = clampNat-near m
  {positiveHeight m D (toℕ x)} {positiveHeight m D (toℕ y)}
  (positive-near-c m D {toℕ x} {toℕ y} (finite-near-nat {m} {x} {y} e))
onVertices (negativeMap m D) x = clampNat m (negativeHeight m D (toℕ x))
preserves (negativeMap m D) {x} {y} e = clampNat-near m
  {negativeHeight m D (toℕ x)} {negativeHeight m D (toℕ y)}
  (negative-near-c m D {toℕ x} {toℕ y} (finite-near-nat {m} {x} {y} e))

-- 其余坐标变化时 D 可能变化。这两条证书处理 c 不变的情况；
-- 完整网格 Φ 仍需证明每条边的两端有共同选面见证。
positiveMap-near-distance : (m : ℕ) {D E : ℕ} → NearNat D E
  → (x : Fin (suc m)) → Near (onVertices (positiveMap m D) x) (onVertices (positiveMap m E) x)
positiveMap-near-distance m {D} {E} e x = clampNat-near m
  {positiveHeight m D (toℕ x)} {positiveHeight m E (toℕ x)}
  (positive-near-D m (toℕ x) {D} {E} e)

negativeMap-near-distance : (m : ℕ) {D E : ℕ} → NearNat D E
  → (x : Fin (suc m)) → Near (onVertices (negativeMap m D) x) (onVertices (negativeMap m E) x)
negativeMap-near-distance m {D} {E} e x = clampNat-near m
  {negativeHeight m D (toℕ x)} {negativeHeight m E (toℕ x)}
  (negative-near-D m (toℕ x) {D} {E} e)

positiveMap-large-distance : (m D : ℕ) → m ≤ D → positiveMap m D ≡ idHom (Iₘ m)
positiveMap-large-distance m D far = homExt λ x →
  cong (clampNat m) (positive-large-distance m D (toℕ x) far) ∙ clamp-inclusion x

negativeMap-large-distance : (m D : ℕ) → m ≤ D → negativeMap m D ≡ idHom (Iₘ m)
negativeMap-large-distance m D far = homExt λ x →
  cong (clampNat m) (negative-large-distance m D (toℕ x) (finite-bound x) far)
  ∙ clamp-inclusion x
