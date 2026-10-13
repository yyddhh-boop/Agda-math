{-# OPTIONS --cubical --safe #-}

module DHH.StableNerve.GridFaces where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma
open import DHH.Graph
open import DHH.Cubes using
  (Position; here; there; CoordinatePair; front; under;
   lower; upper; lowerWide; upperWide)
open import DHH.StableNerve.Interval using (endpoint; threshold; threshold-endpoint)
open import DHH.StableNerve.Grid

-- 坐标算法只沿 Position 的共同前缀递归，不枚举维数或网格顶点。
-- Grid 的面是插入区间端点；删除保留所有其他坐标。
readGridCoordinate : (m : ℕ) {n : ℕ}
  → Position n → Vertex (Grid m n) → Fin (suc m)
readGridCoordinate m here = fst
readGridCoordinate m (there i) (a , x) = readGridCoordinate m i x

grid-read-insert : (m : ℕ) {n : ℕ} (i : Position (suc n))
  (b : Bool) (x : Vertex (Grid m n))
  → readGridCoordinate m i (insertGrid m i b x) ≡ endpoint m b
grid-read-insert m here b x = refl
grid-read-insert m {suc n} (there i) b (a , x) = grid-read-insert m i b x

grid-delete-insert : (m : ℕ) {n : ℕ} (i : Position (suc n))
  (b : Bool) (x : Vertex (Grid m n))
  → deleteGrid m i (insertGrid m i b x) ≡ x
grid-delete-insert m here b x = refl
grid-delete-insert m {suc n} (there i) b (a , x) =
  cong (λ y → a , y) (grid-delete-insert m i b x)

-- 位于指定面上的环境点，删除该坐标再插入端点，恢复原点。
grid-insert-delete-on-face : (m : ℕ) {n : ℕ} (i : Position (suc n))
  (b : Bool) (x : Vertex (Grid m (suc n)))
  → readGridCoordinate m i x ≡ endpoint m b
  → insertGrid m i b (deleteGrid m i x) ≡ x
grid-insert-delete-on-face m here b (a , x) e = cong (λ c → c , x) (sym e)
grid-insert-delete-on-face m {suc n} (there i) b (a , x) e =
  cong (λ y → a , y) (grid-insert-delete-on-face m i b x e)

grid-face-mono : (m : ℕ) {n : ℕ} (i : Position (suc n)) (b : Bool)
  (x y : Vertex (Grid m n))
  → insertGrid m i b x ≡ insertGrid m i b y → x ≡ y
grid-face-mono m i b x y e =
  sym (grid-delete-insert m i b x)
  ∙ cong (deleteGrid m i) e
  ∙ grid-delete-insert m i b y

-- m = suc r 时取第一个阈值即可分辨两个端点；m = 0 不满足此性质。
grid-endpoint-injective : (r : ℕ) (a b : Bool)
  → endpoint (suc r) a ≡ endpoint (suc r) b → a ≡ b
grid-endpoint-injective r a b e =
  sym (threshold-endpoint {m = suc r} fzero a)
  ∙ cong (threshold {m = suc r} fzero) e
  ∙ threshold-endpoint {m = suc r} fzero b

grid-face-endpoint-equal : (r : ℕ) {n : ℕ} (i : Position (suc n))
  (a b : Bool) (x y : Vertex (Grid (suc r) n))
  → insertGrid (suc r) i a x ≡ insertGrid (suc r) i b y → a ≡ b
grid-face-endpoint-equal r i a b x y e = grid-endpoint-injective r a b
  (sym (grid-read-insert (suc r) i a x)
   ∙ cong (readGridCoordinate (suc r) i) e
   ∙ grid-read-insert (suc r) i b y)

-- 两个不同位置由 CoordinatePair 表示：front 处理首个不同位置，
-- under 剥去共同前缀。下面四式适用于非相邻位置及所有有限维数。
grid-insert-distinct : (m : ℕ) {n : ℕ} (p : CoordinatePair n)
  (a b : Bool) (x : Vertex (Grid m n))
  → insertGrid m (lowerWide p) a (insertGrid m (upper p) b x)
    ≡ insertGrid m (upperWide p) b (insertGrid m (lower p) a x)
grid-insert-distinct m (front j) a b x = refl
grid-insert-distinct m (under p) a b (c , x) =
  cong (λ y → c , y) (grid-insert-distinct m p a b x)

grid-delete-distinct : (m : ℕ) {n : ℕ} (p : CoordinatePair n)
  (x : Vertex (Grid m (suc (suc n))))
  → deleteGrid m (upper p) (deleteGrid m (lowerWide p) x)
    ≡ deleteGrid m (lower p) (deleteGrid m (upperWide p) x)
grid-delete-distinct m (front j) (a , x) = refl
grid-delete-distinct m (under p) (a , x) =
  cong (λ y → a , y) (grid-delete-distinct m p x)

grid-delete-insert-upper : (m : ℕ) {n : ℕ} (p : CoordinatePair n)
  (b : Bool) (x : Vertex (Grid m (suc n)))
  → deleteGrid m (lowerWide p) (insertGrid m (upperWide p) b x)
    ≡ insertGrid m (upper p) b (deleteGrid m (lower p) x)
grid-delete-insert-upper m (front j) b (a , x) = refl
grid-delete-insert-upper m (under p) b (a , x) =
  cong (λ y → a , y) (grid-delete-insert-upper m p b x)

grid-delete-insert-lower : (m : ℕ) {n : ℕ} (p : CoordinatePair n)
  (a : Bool) (x : Vertex (Grid m (suc n)))
  → deleteGrid m (upperWide p) (insertGrid m (lowerWide p) a x)
    ≡ insertGrid m (lower p) a (deleteGrid m (upper p) x)
grid-delete-insert-lower m (front j) a x = refl
grid-delete-insert-lower m (under p) a (b , x) =
  cong (λ y → b , y) (grid-delete-insert-lower m p a x)

-- 环境网格中相同的两个面点，实际来自共同的余维二网格点。
-- 共同点由删除构造，输出两个恢复等式；没有选择顶点的规范表示。
GridDistinctFactorization : (m : ℕ) {n : ℕ} (p : CoordinatePair n)
  (a b : Bool) (x y : Vertex (Grid m (suc n))) → Type₀
GridDistinctFactorization m {n} p a b x y = Σ[ z ∈ Vertex (Grid m n) ]
  (x ≡ insertGrid m (upper p) b z) × (y ≡ insertGrid m (lower p) a z)

grid-distinct-face-factorization : (m : ℕ) {n : ℕ} (p : CoordinatePair n)
  (a b : Bool) (x y : Vertex (Grid m (suc n)))
  → insertGrid m (lowerWide p) a x ≡ insertGrid m (upperWide p) b y
  → GridDistinctFactorization m p a b x y
grid-distinct-face-factorization m {n} p a b x y e = z , x-factor , y-factor
  where
  z : Vertex (Grid m n)
  z = deleteGrid m (upper p) x

  y-factor : y ≡ insertGrid m (lower p) a z
  y-factor = sym (grid-delete-insert m (upperWide p) b y)
    ∙ sym (cong (deleteGrid m (upperWide p)) e)
    ∙ grid-delete-insert-lower m p a x

  x-factor : x ≡ insertGrid m (upper p) b z
  x-factor = sym (grid-delete-insert m (lowerWide p) a x)
    ∙ cong (deleteGrid m (lowerWide p)) e
    ∙ cong (λ v → deleteGrid m (lowerWide p) (insertGrid m (upperWide p) b v)) y-factor
    ∙ grid-delete-insert-upper m p b (insertGrid m (lower p) a z)
    ∙ cong (insertGrid m (upper p) b) (grid-delete-insert m (lower p) a z)
