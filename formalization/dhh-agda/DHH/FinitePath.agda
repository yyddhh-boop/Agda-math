{-# OPTIONS --cubical --safe #-}

module DHH.FinitePath where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Fin using (Fin; toℕ; toℕ-injective; isSetFin; finj; fsuc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph

-- I_m has m+1 vertices: 0,...,m.  The truncation makes adjacency a
-- proposition, independently of how a loop or a neighbouring pair
-- was witnessed.  This works uniformly for every finite length m.
Near : ℕ → ℕ → Type
Near x y = ∥ (x ≡ y) ⊎ ((suc x ≡ y) ⊎ (x ≡ suc y)) ∥₁

nearSym : {x y : ℕ} → Near x y → Near y x
nearSym = PT.rec squash₁ λ where
  (inl p) → ∣ inl (sym p) ∣₁
  (inr (inl p)) → ∣ inr (inr (sym p)) ∣₁
  (inr (inr p)) → ∣ inr (inl (sym p)) ∣₁

PathGraph : ℕ → Graph ℓ-zero
Vertex (PathGraph m) = Fin (suc m)
vertex-isSet (PathGraph m) = isSetFin
Adj (PathGraph m) x y = Near (toℕ x) (toℕ y)
adj-isProp (PathGraph m) _ _ = squash₁
adj-refl (PathGraph m) _ = ∣ inl refl ∣₁
adj-sym (PathGraph m) = nearSym

extend : (m : ℕ) → Hom (PathGraph m) (PathGraph (suc m))
onVertices (extend m) = finj
preserves (extend m) e = e

shift : (m : ℕ) → Hom (PathGraph m) (PathGraph (suc m))
onVertices (shift m) = fsuc
preserves (shift m) = PT.rec squash₁ λ where
  (inl p) → ∣ inl (cong suc p) ∣₁
  (inr (inl p)) → ∣ inr (inl (cong suc p)) ∣₁
  (inr (inr p)) → ∣ inr (inr (cong suc p)) ∣₁

-- A finite vertex string gives a graph path precisely when every
-- consecutive pair is adjacent; repetitions require no extra premise.
pathFromString : ∀ {ℓ} {G : Graph ℓ} (m : ℕ)
               → (f : Fin (suc m) → Vertex G)
               → ((x y : Fin (suc m)) → suc (toℕ x) ≡ toℕ y
                  → Adj G (f x) (f y))
               → Hom (PathGraph m) G
onVertices (pathFromString m f next) = f
preserves (pathFromString {G = G} m f next) {x} {y} =
  PT.rec (adj-isProp G _ _) λ where
    (inl p) → subst (λ z → Adj G (f x) (f z))
                    (toℕ-injective p) (adj-refl G (f x))
    (inr (inl p)) → next x y p
    (inr (inr p)) → adj-sym G (next y x (sym p))

stringFromPath : ∀ {ℓ} {G : Graph ℓ} {m : ℕ}
               → (f : Hom (PathGraph m) G)
               → (x y : Fin (suc m)) → suc (toℕ x) ≡ toℕ y
               → Adj G (onVertices f x) (onVertices f y)
stringFromPath f x y p = preserves f ∣ inr (inl p) ∣₁
