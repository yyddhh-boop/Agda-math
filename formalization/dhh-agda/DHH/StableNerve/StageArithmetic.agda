{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.StageArithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; predℕ; isSetℕ)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ≤-suc; ≤-sucℕ; isProp≤; ¬m<m)
open import Cubical.Data.Sigma using (_,_)
import Cubical.Data.Empty as Empty
open import DHH.CubicalNerve

-- Later 是“从 k 走到 l 的有限步数”的结构化证书。
-- 它使计算直接递归于 now/next，而不是不断猜测截断存在的代表。
data Later (k : ℕ) : ℕ → Type₀ where
  now : Later k k
  next : {l : ℕ} → Later k l → Later k (suc l)

laterLe : {k l : ℕ} → Later k l → k ≤ l
laterLe now = ≤-refl
laterLe (next p) = ≤-suc (laterLe p)

lengthLater : (k d : ℕ) → Later k (d + k)
lengthLater k zero = now
lengthLater k (suc d) = next (lengthLater k d)

fromLe : {k l : ℕ} → k ≤ l → Later k l
fromLe {k} (d , e) = subst (Later k) e (lengthLater k d)

-- 两个末指标先保持独立，避免 without-K 下对 Later k k 作非法双重匹配。
-- 自然数本身是集合；只用这个已证明事实校正末指标路径，不假定 K。
later-path : {k l m : ℕ} (p : Later k l) (q : Later k m) (e : l ≡ m)
  → PathP (λ i → Later k (e i)) p q
later-path {k = k} now now e =
  subst (λ h → PathP (λ i → Later k (h i)) now now) (isSetℕ k k refl e) refl
later-path now (next {l = m} q) e = Empty.rec
  (¬m<m (subst (_≤ m) e (laterLe q)))
later-path (next {l = l} p) now e = Empty.rec
  (¬m<m (subst (_≤ l) (sym e) (laterLe p)))
later-path {k = k} (next {l = l} p) (next {l = m} q) e =
  subst (λ h → PathP (λ i → Later k (h i)) (next p) (next q))
    (isSetℕ (suc l) (suc m) (cong suc (cong predℕ e)) e)
    (λ i → next (later-path p q (cong predℕ e) i))

later-isProp : {k l : ℕ} → isProp (Later k l)
later-isProp p q = later-path p q refl

laterTrans : {k l m : ℕ} → Later k l → Later l m → Later k m
laterTrans p now = p
laterTrans p (next q) = next (laterTrans p q)

private variable ℓ : Level
module Stages (A : ℕ → CubicalSet ℓ)
              (s : (k : ℕ) → CubicalNatural (A k) (A (suc k))) where

  laterMap : {k l : ℕ} → Later k l → CubicalNatural (A k) (A l)
  laterMap {k} now = cubicalId (A k)
  laterMap (next {l} p) = laterMap p ⋆n s l

  laterMap-compose : {k l m : ℕ} (p : Later k l) (q : Later l m)
    → laterMap (laterTrans p q) ≡ laterMap p ⋆n laterMap q
  laterMap-compose p now = cubicalNaturalExt (λ _ _ → refl)
  laterMap-compose p (next {l} q) = cubicalNaturalExt λ n c →
    cong (mapCells (s l) n)
      (cong (λ f → mapCells f n c) (laterMap-compose p q))

  advance : {k l : ℕ} → k ≤ l → CubicalNatural (A k) (A l)
  advance p = laterMap (fromLe p)

  advanceCell : {k l : ℕ} → k ≤ l → (n : ℕ) → Cell (A k) n → Cell (A l) n
  advanceCell p n = mapCells (advance p) n

  -- 同一比较 k≤l 的证书是命题：选不同步数证明不会改变 cell。
  advanceCell-proof-irrelevant : {k l : ℕ} (p q : k ≤ l) (n : ℕ) (c : Cell (A k) n)
    → advanceCell p n c ≡ advanceCell q n c
  advanceCell-proof-irrelevant p q n c = cong (λ r → advanceCell r n c) (isProp≤ p q)

  advanceCell-id : (k n : ℕ) (c : Cell (A k) n)
    → advanceCell ≤-refl n c ≡ c
  advanceCell-id k n c = cong (λ r → mapCells (laterMap r) n c)
    (later-isProp (fromLe ≤-refl) now)

  advanceCell-step : (k n : ℕ) (c : Cell (A k) n)
    → advanceCell ≤-sucℕ n c ≡ mapCells (s k) n c
  advanceCell-step k n c = cong (λ r → mapCells (laterMap r) n c)
    (later-isProp (fromLe ≤-sucℕ) (next now))

  advanceCell-compose : {k l m : ℕ} (p : k ≤ l) (q : l ≤ m) (n : ℕ) (c : Cell (A k) n)
    → advanceCell (≤-trans p q) n c ≡ advanceCell q n (advanceCell p n c)
  advanceCell-compose p q n c =
    cong (λ r → mapCells (laterMap r) n c)
      (later-isProp (fromLe (≤-trans p q)) (laterTrans (fromLe p) (fromLe q)))
    ∙ cong (λ f → mapCells f n c) (laterMap-compose (fromLe p) (fromLe q))

  advance-id : (k : ℕ) → advance (≤-refl {m = k}) ≡ cubicalId (A k)
  advance-id k = cubicalNaturalExt (advanceCell-id k)

  advance-step : (k : ℕ) → advance (≤-sucℕ {n = k}) ≡ s k
  advance-step k = cubicalNaturalExt (advanceCell-step k)

  advance-compose : {k l m : ℕ} (p : k ≤ l) (q : l ≤ m)
    → advance (≤-trans p q) ≡ advance p ⋆n advance q
  advance-compose p q = cubicalNaturalExt (advanceCell-compose p q)
