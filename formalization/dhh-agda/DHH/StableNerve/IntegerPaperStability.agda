{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerPaperStability where

-- 对照 2306.02218v1 §12：每个坐标、每个正负方向分别存在一个
-- 自然阈值，超过阈值后保持其它坐标任意时函数值不变。
-- 本模块以 M+d 编码半直线；d=0 的等式自反，因此与严格超过 M
-- 的论文量词完全同一条件。有限维 recFin 合并阈值，不用无限选择。

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; compIso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-zero; +-suc; +-comm; +-assoc)
open import Cubical.Data.Nat.Order using (_≤_; ≤SumLeft; ≤SumRight; ≤-trans; ≤-suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc; predℤ; predSuc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.CubicalNerve using (Cell; mapCells)
open import DHH.StableNerve.Colimit using (N∞; N∞-map)
open import DHH.StableNerve.IntegerInterval
open import DHH.StableNerve.CenteredInterval
open import DHH.StableNerve.IntegerStable
open import DHH.StableNerve.IntegerDirections

private variable ℓ ℓ' : Level

negative : ℕ → ℤ
negative zero = pos zero
negative (suc a) = negsuc a

signed : Bool → ℕ → ℤ
signed false = negative
signed true = pos

down-negative : (a d : ℕ) → down a (negsuc d) ≡ negsuc (a + d)
down-negative zero d = refl
down-negative (suc a) d = cong predℤ (down-negative a d)

down-zero : (a : ℕ) → down a (pos zero) ≡ negative a
down-zero zero = refl
down-zero (suc zero) = refl
down-zero (suc (suc a)) = cong predℤ (down-zero (suc a))

down-pos-shift : (a t : ℕ) → down a (pos (a + t)) ≡ pos t
down-pos-shift zero t = refl
down-pos-shift (suc a) t = cong predℤ (down-suc a (pos (a + t)))
  ∙ predSuc (down a (pos (a + t))) ∙ down-pos-shift a t

swap-prefix : (a b d : ℕ) → a + (b + d) ≡ b + (a + d)
swap-prefix a b d = +-assoc a b d ∙ cong (_+ d) (+-comm a b) ∙ sym (+-assoc b a d)

positive-upper-ray : (a m d : ℕ) → down a (pos (m + (a + d))) ≡ pos (m + d)
positive-upper-ray a m d = cong (λ t → down a (pos t)) (swap-prefix m a d)
  ∙ down-pos-shift a (m + d)

double-plus : (a : ℕ) → double a ≡ a + a
double-plus zero = refl
double-plus (suc a) = cong (λ t → suc (suc t)) (double-plus a)
  ∙ sym (cong suc (+-suc a a))

DirectionData : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y)
  → Fin n → Bool → ℕ → Type ℓ
DirectionData {n = n} f i b M = (d : ℕ) (x : Vertex (IntegerGrid n))
  → f (replaceCoordinate i (signed b (M + d)) x)
    ≡ f (replaceCoordinate i (signed b M) x)

StrictDirectionData : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y)
  → Fin n → Bool → ℕ → Type ℓ
StrictDirectionData {n = n} f i b M = (d : ℕ) (x : Vertex (IntegerGrid n))
  → f (replaceCoordinate i (signed b (M + suc d)) x)
    ≡ f (replaceCoordinate i (signed b M) x)

direction-to-strict : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y)
  (i : Fin n) (b : Bool) (M : ℕ)
  → DirectionData f i b M → StrictDirectionData f i b M
direction-to-strict f i b M h d x = h (suc d) x

strict-to-direction : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y)
  (i : Fin n) (b : Bool) (M : ℕ)
  → StrictDirectionData f i b M → DirectionData f i b M
strict-to-direction f i b M h zero x =
  cong (λ t → f (replaceCoordinate i (signed b t) x)) (+-zero M)
strict-to-direction f i b M h (suc d) x = h d x

PaperStable : {G : Graph ℓ} {n : ℕ} → Hom (IntegerGrid n) G → Type ℓ
PaperStable {n = n} f = (i : Fin n) (b : Bool)
  → ∥ Σ[ M ∈ ℕ ] DirectionData (onVertices f) i b M ∥₁

paperStable-isProp : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → isProp (PaperStable {n = n} f)
paperStable-isProp f = isPropΠ2 (λ _ _ → squash₁)

-- 增大一个阈值时，两端都与旧阈值比较。证明只用自然数加法，
-- 故可对正/负两方向复用，且不依赖图映射相等是否可判定。
grow-direction : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y)
  (i : Fin n) (b : Bool) {M B : ℕ} → M ≤ B
  → DirectionData f i b M → DirectionData f i b B
grow-direction f i b {M} {B} (e , p) h d x =
  cong (λ t → f (replaceCoordinate i (signed b t) x))
    (cong (_+ d) (sym p) ∙ sym (+-assoc e M d) ∙ swap-prefix e M d)
  ∙ h (e + d) x
  ∙ sym (cong (λ t → f (replaceCoordinate i (signed b t) x))
    (sym p ∙ +-comm e M) ∙ h e x)

ray-window-to-direction : {n : ℕ} {Y : Type ℓ} (k : ℕ)
  (f : Vertex (IntegerGrid n) → Y) → RayWindow k f
  → (i : Fin n) (b : Bool) → Σ[ M ∈ ℕ ] DirectionData f i b M
ray-window-to-direction k f h i false = suc (offset k) , λ d x →
  cong (λ z → f (replaceCoordinate i z x)) (sym (down-negative (offset k) d))
  ∙ lowerRay h i d x ∙ sym (lowerRay h i zero x)
  ∙ cong (λ z → f (replaceCoordinate i z x)) (down-negative (offset k) zero)
  ∙ cong (λ t → f (replaceCoordinate i (negsuc t) x)) (+-zero (offset k))
ray-window-to-direction k f h i true = suc k , λ d x →
  cong (λ z → f (replaceCoordinate i z x)) (sym (positive-upper-ray (offset k) (suc k) d))
  ∙ upperRay h i (offset k + d) x ∙ sym (upperRay h i (offset k) x)
  ∙ cong (λ z → f (replaceCoordinate i z x))
    (cong (λ t → down (offset k) (pos (suc k + t))) (sym (+-zero (offset k)))
      ∙ positive-upper-ray (offset k) (suc k) zero)
  ∙ cong (λ t → f (replaceCoordinate i (pos t) x)) (+-zero (suc k))

ray-to-paper-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → RayStable {n = n} f → PaperStable {n = n} f
ray-to-paper-stable f = PT.rec (paperStable-isProp f)
  (λ { (k , h) i b → ∣ ray-window-to-direction k (onVertices f) h i b ∣₁ })

sumBounds : {n : ℕ} → (Fin n → ℕ) → ℕ
sumBounds {zero} xs = zero
sumBounds {suc n} xs = xs fzero + sumBounds (λ i → xs (fsuc i))

bounded-by-sum : {n : ℕ} (xs : Fin n → ℕ) (i : Fin n) → xs i ≤ sumBounds xs
bounded-by-sum {suc n} xs fzero = ≤SumLeft
bounded-by-sum {suc n} xs (fsuc i) =
  ≤-trans (bounded-by-sum (λ j → xs (fsuc j)) i) ≤SumRight

balanced-lower-end : (M : ℕ)
  → down (offset (suc (double M))) (pos zero) ≡ negative (suc M)
balanced-lower-end M = cong (λ a → down a (pos zero)) (offset-suc-double M)
  ∙ down-zero (suc M)

balanced-lower-ray : (M d : ℕ)
  → down (offset (suc (double M))) (negsuc d) ≡ negative (suc M + suc d)
balanced-lower-ray M d = cong (λ a → down a (negsuc d)) (offset-suc-double M)
  ∙ down-negative (suc M) d ∙ sym (cong negative (+-suc (suc M) d))

balanced-upper-ray : (M d : ℕ)
  → down (offset (suc (double M))) (pos (suc (suc (double M)) + d))
    ≡ pos (suc M + d)
balanced-upper-ray M d =
  cong (λ a → down a (pos (suc (suc (double M)) + d))) (offset-suc-double M)
  ∙ cong (λ t → down (suc M) (pos (t + d))) (double-plus (suc M))
  ∙ cong (λ t → down (suc M) (pos t)) (sym (+-assoc (suc M) (suc M) d))
  ∙ down-pos-shift (suc M) (suc M + d)

balanced-upper-end : (M : ℕ)
  → down (offset (suc (double M))) (pos (suc (suc (double M)))) ≡ pos (suc M)
balanced-upper-end M =
  cong (λ t → down (offset (suc (double M))) (pos t))
    (sym (+-zero (suc (suc (double M)))))
  ∙ balanced-upper-ray M zero ∙ cong pos (+-zero (suc M))

balancedWindow : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y) (M : ℕ)
  → ((i : Fin n) (b : Bool) → DirectionData f i b (suc M))
  → RayWindow {n = n} (suc (double M)) f
lowerRay (balancedWindow f M h) i d x =
  cong (λ z → f (replaceCoordinate i z x)) (balanced-lower-ray M d)
  ∙ h i false (suc d) x
  ∙ cong (λ z → f (replaceCoordinate i z x)) (sym (balanced-lower-end M))
upperRay (balancedWindow f M h) i d x =
  cong (λ z → f (replaceCoordinate i z x)) (balanced-upper-ray M d)
  ∙ h i true d x
  ∙ cong (λ z → f (replaceCoordinate i z x)) (sym (balanced-upper-end M))

DirectionPair : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y) (i : Fin n) → Type ℓ
DirectionPair f i = (Σ[ M ∈ ℕ ] DirectionData f i false M)
  × (Σ[ M ∈ ℕ ] DirectionData f i true M)

-- 对 2n 个阈值取一个有限和，再加一步；每个阈值都不超过它。
-- 有界性按 Fin 的构造递归，输入方向可能有不同的原始阈值。
combineDirections : {n : ℕ} {Y : Type ℓ} (f : Vertex (IntegerGrid n) → Y)
  → ((i : Fin n) → DirectionPair {n = n} f i)
  → Σ[ k ∈ ℕ ] RayWindow {n = n} k f
combineDirections {n = n} f ds = suc (double M) , balancedWindow {n = n} f M grown
  where
  xs : Fin n → ℕ
  xs i = fst (fst (ds i)) + fst (snd (ds i))
  M : ℕ
  M = sumBounds xs
  grown : (i : Fin n) (b : Bool) → DirectionData f i b (suc M)
  grown i false = grow-direction f i false
    (≤-suc (≤-trans ≤SumLeft (bounded-by-sum xs i))) (snd (fst (ds i)))
  grown i true = grow-direction f i true
    (≤-suc (≤-trans ≤SumRight (bounded-by-sum xs i))) (snd (snd (ds i)))

paper-to-ray-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → PaperStable {n = n} f → RayStable {n = n} f
paper-to-ray-stable {n = n} f p = PT.recFin {m = n}
  {P = DirectionPair {n = n} (onVertices f)} squash₁
  (λ ds → ∣ combineDirections {n = n} (onVertices f) ds ∣₁)
  (λ i → PT.rec2 squash₁ (λ a b → ∣ a , b ∣₁) (p i false) (p i true))

window-to-paper-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → WindowStable {n = n} f → PaperStable {n = n} f
window-to-paper-stable f p = ray-to-paper-stable f (window-to-ray-stable f p)

paper-to-window-stable : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → PaperStable {n = n} f → WindowStable {n = n} f
paper-to-window-stable f p = ray-to-window-stable f (paper-to-ray-stable f p)

windowPaperIso : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → Iso (WindowStable {n = n} f) (PaperStable {n = n} f)
Iso.fun (windowPaperIso f) = window-to-paper-stable f
Iso.inv (windowPaperIso f) = paper-to-window-stable f
Iso.rightInv (windowPaperIso f) p = paperStable-isProp f _ p
Iso.leftInv (windowPaperIso f) p = squash₁ _ p

windowPaperEquivalence : {G : Graph ℓ} {n : ℕ} (f : Hom (IntegerGrid n) G)
  → WindowStable {n = n} f ≃ PaperStable {n = n} f
windowPaperEquivalence f = isoToEquiv (windowPaperIso f)

PaperIntegerCell : (G : Graph ℓ) (n : ℕ) → Type ℓ
PaperIntegerCell G n = Σ[ f ∈ Hom (IntegerGrid n) G ] PaperStable {n = n} f

paperCellIso : (G : Graph ℓ) (n : ℕ) → Iso (StableIntegerCell G n) (PaperIntegerCell G n)
Iso.fun (paperCellIso G n) (f , p) = f , window-to-paper-stable f p
Iso.inv (paperCellIso G n) (f , p) = f , paper-to-window-stable f p
Iso.rightInv (paperCellIso G n) (f , p) = Σ≡Prop (λ f → paperStable-isProp f) refl
Iso.leftInv (paperCellIso G n) (f , p) = Σ≡Prop (λ _ → squash₁) refl

-- 已完成的是所有图、所有维数的实际 cell 等价，且正向保留同一个
-- 整数图映射。神经的 faces/connections 全自然性与 Kan 填充仍另列。
colimitPaperCellIso : (G : Graph ℓ) (n : ℕ) → Iso (Cell (N∞ G) n) (PaperIntegerCell G n)
colimitPaperCellIso G n = compIso (IntegerComparison.integerCellIso G n) (paperCellIso G n)

colimitPaperCellEquivalence : (G : Graph ℓ) (n : ℕ) → Cell (N∞ G) n ≃ PaperIntegerCell G n
colimitPaperCellEquivalence G n = isoToEquiv (colimitPaperCellIso G n)

paperIntegerMap : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H) (n : ℕ)
  → PaperIntegerCell G n → PaperIntegerCell H n
paperIntegerMap h n (f , p) = h ∘g f , λ i b → PT.rec squash₁
  (λ { (M , q) → ∣ M , (λ d x → cong (onVertices h) (q d x)) ∣₁ }) (p i b)

colimitPaperCell-natural : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H) (n : ℕ)
  (c : Cell (N∞ G) n)
  → Iso.fun (colimitPaperCellIso H n) (mapCells (N∞-map h) n c)
    ≡ paperIntegerMap h n (Iso.fun (colimitPaperCellIso G n) c)
colimitPaperCell-natural h n c = Σ≡Prop (λ f → paperStable-isProp f)
  (integerHom-natural h n c)
