{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerDirections where

-- 本模块把「整个网格投影不改变 f」拆为有限个逐坐标截断等式。
-- 递归参数是维数；每一步只截断一个坐标并保持其余坐标。
-- 这关闭整窗口与逐坐标表述之间的差别；IntegerPaperStability
-- 将这里的两条射线与论文各方向独立阈值进一步作完整比较。

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.StableNerve.Interval using (top)
open import DHH.StableNerve.IntegerInterval
open import DHH.StableNerve.IntegerClamp using (clamp; clampNat; clamp-at-or-above)
open import DHH.StableNerve.CenteredInterval
open import DHH.StableNerve.IntegerStable

private variable ℓ : Level

scalarProjection : (k : ℕ) → ℤ → ℤ
scalarProjection k z = onVertices (centeredInclusion k) (onVertices (centeredClamp k) z)

scalarProjection-idempotent : (k : ℕ) (z : ℤ)
  → scalarProjection k (scalarProjection k z) ≡ scalarProjection k z
scalarProjection-idempotent k z = cong (onVertices (centeredInclusion k))
  (cong (λ h → onVertices h (onVertices (centeredClamp k) z)) (centered-retraction k))

clipCoordinate : {n : ℕ} (k : ℕ) → Fin n → Vertex (IntegerGrid n) → Vertex (IntegerGrid n)
clipCoordinate {suc n} k fzero (z , x) = scalarProjection k z , x
clipCoordinate {suc n} k (fsuc i) (z , x) = z , clipCoordinate k i x

clipAll : (k n : ℕ) → Vertex (IntegerGrid n) → Vertex (IntegerGrid n)
clipAll k n = onVertices (windowProjection k n)

clipAll-coordinate : {n : ℕ} (k : ℕ) (i : Fin n) (x : Vertex (IntegerGrid n))
  → clipAll k n (clipCoordinate k i x) ≡ clipAll k n x
clipAll-coordinate {suc n} k fzero (z , x) = cong (λ a → a , clipAll k n x)
  (scalarProjection-idempotent k z)
clipAll-coordinate {suc n} k (fsuc i) (z , x) =
  cong (λ y → scalarProjection k z , y) (clipAll-coordinate k i x)

CoordinateWindow : {n : ℕ} (k : ℕ) {Y : Type ℓ}
  → (Vertex (IntegerGrid n) → Y) → Type ℓ
CoordinateWindow {n = n} k f = (i : Fin n) (x : Vertex (IntegerGrid n))
  → f x ≡ f (clipCoordinate k i x)

-- 一次截断首坐标，再将同一个问题交给剩余 n 个坐标。
-- 只有有限维递归；等式直接保持全部其它坐标，未枚举整数顶点。
coordinates-to-all : (k n : ℕ) {Y : Type ℓ}
  (f : Vertex (IntegerGrid n) → Y) → CoordinateWindow {n = n} k f
  → (x : Vertex (IntegerGrid n)) → f x ≡ f (clipAll k n x)
coordinates-to-all k zero f p x = refl
coordinates-to-all k (suc n) f p (z , x) = p fzero (z , x)
  ∙ coordinates-to-all k n (λ y → f (scalarProjection k z , y))
    (λ i y → p (fsuc i) (scalarProjection k z , y)) x

all-to-coordinates : (k n : ℕ) {Y : Type ℓ}
  (f : Vertex (IntegerGrid n) → Y)
  → ((x : Vertex (IntegerGrid n)) → f (clipAll k n x) ≡ f x)
  → CoordinateWindow {n = n} k f
all-to-coordinates k n f p i x = sym (p x)
  ∙ cong f (sym (clipAll-coordinate k i x)) ∙ p (clipCoordinate k i x)

CoordinateStable : {G : Graph ℓ} {n : ℕ} → Hom (IntegerGrid n) G → Type ℓ
CoordinateStable {n = n} f = ∥ Σ[ k ∈ ℕ ] CoordinateWindow {n = n} k (onVertices f) ∥₁

window-to-coordinate-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → WindowStable {n = n} f → CoordinateStable {n = n} f
window-to-coordinate-stable {n = n} f = PT.rec squash₁ λ { (k , p) →
  ∣ k , all-to-coordinates k n (onVertices f) (λ x → cong (λ h → onVertices h x) p) ∣₁ }

coordinate-to-window-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → CoordinateStable {n = n} f → WindowStable {n = n} f
coordinate-to-window-stable {G = G} {n = n} f = PT.rec squash₁ λ { (k , p) →
  ∣ k , homExt {G = IntegerGrid n} {H = G}
    (λ x → sym (coordinates-to-all k n (onVertices f) p x)) ∣₁ }

windowCoordinateIso : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → Iso (WindowStable {n = n} f) (CoordinateStable {n = n} f)
Iso.fun (windowCoordinateIso f) = window-to-coordinate-stable f
Iso.inv (windowCoordinateIso f) = coordinate-to-window-stable f
Iso.rightInv (windowCoordinateIso f) p = squash₁ _ p
Iso.leftInv (windowCoordinateIso f) p = squash₁ _ p

windowCoordinateEquivalence : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → WindowStable {n = n} f ≃ CoordinateStable {n = n} f
windowCoordinateEquivalence f = isoToEquiv (windowCoordinateIso f)

replaceCoordinate : {n : ℕ} → Fin n → ℤ → Vertex (IntegerGrid n) → Vertex (IntegerGrid n)
replaceCoordinate {suc n} fzero a (z , x) = a , x
replaceCoordinate {suc n} (fsuc i) a (z , x) = z , replaceCoordinate i a x

readCoordinate : {n : ℕ} → Fin n → Vertex (IntegerGrid n) → ℤ
readCoordinate {suc n} fzero (z , x) = z
readCoordinate {suc n} (fsuc i) (z , x) = readCoordinate i x

replace-current : {n : ℕ} (i : Fin n) (x : Vertex (IntegerGrid n))
  → replaceCoordinate i (readCoordinate i x) x ≡ x
replace-current {suc n} fzero (z , x) = refl
replace-current {suc n} (fsuc i) (z , x) = cong (λ y → z , y) (replace-current i x)

clip-replace : {n : ℕ} (k : ℕ) (i : Fin n) (a : ℤ) (x : Vertex (IntegerGrid n))
  → clipCoordinate k i (replaceCoordinate i a x)
    ≡ replaceCoordinate i (scalarProjection k a) x
clip-replace {suc n} k fzero a (z , x) = refl
clip-replace {suc n} k (fsuc i) a (z , x) = cong (λ y → z , y) (clip-replace k i a x)

clip-as-replace : {n : ℕ} (k : ℕ) (i : Fin n) (x : Vertex (IntegerGrid n))
  → clipCoordinate k i x ≡ replaceCoordinate i (scalarProjection k (readCoordinate i x)) x
clip-as-replace {suc n} k fzero (z , x) = refl
clip-as-replace {suc n} k (fsuc i) (z , x) = cong (λ y → z , y) (clip-as-replace k i x)

scalar-lower-ray : (k d : ℕ)
  → scalarProjection k (down (offset k) (negsuc d)) ≡ down (offset k) (pos zero)
scalar-lower-ray k d = cong (onVertices (centeredInclusion k))
  (shiftedClamp-lower-ray (offset k) (suc k) d)

scalar-upper-ray : (k d : ℕ)
  → scalarProjection k (down (offset k) (pos (suc k + d))) ≡ down (offset k) (pos (suc k))
scalar-upper-ray k d = cong (onVertices (centeredInclusion k))
  (shiftedClamp-upper-ray (offset k) (suc k) d)
  ∙ cong (down (offset k)) (finiteToInteger-top (suc k))

-- RayWindow 用真正的整数射线表达常值，且所有其它坐标保持任意。
-- 正负边界来自实际居中窗口；独立论文阈值到 k 的有限合并证明
-- 位于 IntegerPaperStability，保持本模块专注实际逐坐标等式。
record RayWindow {n : ℕ} (k : ℕ) {Y : Type ℓ}
  (f : Vertex (IntegerGrid n) → Y) : Type ℓ where
  field
    lowerRay : (i : Fin n) (d : ℕ) (x : Vertex (IntegerGrid n))
      → f (replaceCoordinate i (down (offset k) (negsuc d)) x)
        ≡ f (replaceCoordinate i (down (offset k) (pos zero)) x)
    upperRay : (i : Fin n) (d : ℕ) (x : Vertex (IntegerGrid n))
      → f (replaceCoordinate i (down (offset k) (pos (suc k + d))) x)
        ≡ f (replaceCoordinate i (down (offset k) (pos (suc k))) x)
open RayWindow public

coordinates-to-rays : {n : ℕ} (k : ℕ) {Y : Type ℓ}
  (f : Vertex (IntegerGrid n) → Y) → CoordinateWindow {n = n} k f → RayWindow k f
lowerRay (coordinates-to-rays k f p) i d x =
  p i (replaceCoordinate i (down (offset k) (negsuc d)) x)
    ∙ cong f (clip-replace k i (down (offset k) (negsuc d)) x)
    ∙ cong (λ z → f (replaceCoordinate i z x)) (scalar-lower-ray k d)
upperRay (coordinates-to-rays k f p) i d x =
  p i (replaceCoordinate i (down (offset k) (pos (suc k + d))) x)
    ∙ cong f (clip-replace k i (down (offset k) (pos (suc k + d))) x)
    ∙ cong (λ z → f (replaceCoordinate i z x)) (scalar-upper-ray k d)

translated-rays-to-projection : (a m : ℕ) {Y : Type ℓ} (g : ℤ → Y)
  → ((d : ℕ) → g (down a (negsuc d)) ≡ g (down a (pos zero)))
  → ((d : ℕ) → g (down a (pos (m + d))) ≡ g (down a (pos m)))
  → (t : ℤ) → g (down a t) ≡ g (down a (finiteToInteger (clamp m t)))
translated-rays-to-projection a m g lo hi (negsuc d) = lo d
translated-rays-to-projection a m g lo hi (pos t) with clampNat-case m t
... | inl p = cong (λ z → g (down a z)) (sym p)
... | inr (d , p) = cong (λ s → g (down a (pos s))) p ∙ hi d
  ∙ cong (λ z → g (down a z))
    (sym (cong finiteToInteger
      (cong (λ s → clamp m (pos s)) p ∙ clamp-at-or-above m d)
      ∙ finiteToInteger-top m))

rays-to-scalar : (k : ℕ) {Y : Type ℓ} (g : ℤ → Y)
  → ((d : ℕ) → g (down (offset k) (negsuc d)) ≡ g (down (offset k) (pos zero)))
  → ((d : ℕ) → g (down (offset k) (pos (suc k + d))) ≡ g (down (offset k) (pos (suc k))))
  → (z : ℤ) → g z ≡ g (scalarProjection k z)
rays-to-scalar k g lo hi z = cong g (sym (down-up (offset k) z))
  ∙ translated-rays-to-projection (offset k) (suc k) g lo hi (up (offset k) z)

rays-to-coordinates : {n : ℕ} (k : ℕ) {Y : Type ℓ}
  (f : Vertex (IntegerGrid n) → Y) → RayWindow k f → CoordinateWindow {n = n} k f
rays-to-coordinates k f p i x = cong f (sym (replace-current i x))
  ∙ rays-to-scalar k (λ z → f (replaceCoordinate i z x))
    (λ d → lowerRay p i d x) (λ d → upperRay p i d x) (readCoordinate i x)
  ∙ cong f (sym (clip-as-replace k i x))

RayStable : {G : Graph ℓ} {n : ℕ} → Hom (IntegerGrid n) G → Type ℓ
RayStable {n = n} f = ∥ Σ[ k ∈ ℕ ] RayWindow {n = n} k (onVertices f) ∥₁

window-to-ray-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → WindowStable {n = n} f → RayStable {n = n} f
window-to-ray-stable {n = n} f p = PT.rec squash₁
  (λ { (k , c) → ∣ k , coordinates-to-rays k (onVertices f) c ∣₁ })
  (window-to-coordinate-stable f p)

ray-to-window-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → RayStable {n = n} f → WindowStable {n = n} f
ray-to-window-stable {n = n} f p = coordinate-to-window-stable f
  (PT.rec squash₁ (λ { (k , c) → ∣ k , rays-to-coordinates k (onVertices f) c ∣₁ }) p)

windowRayIso : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → Iso (WindowStable {n = n} f) (RayStable {n = n} f)
Iso.fun (windowRayIso f) = window-to-ray-stable f
Iso.inv (windowRayIso f) = ray-to-window-stable f
Iso.rightInv (windowRayIso f) p = squash₁ _ p
Iso.leftInv (windowRayIso f) p = squash₁ _ p

windowRayEquivalence : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → WindowStable {n = n} f ≃ RayStable {n = n} f
windowRayEquivalence f = isoToEquiv (windowRayIso f)
