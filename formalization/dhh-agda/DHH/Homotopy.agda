{-# OPTIONS --cubical --safe #-}

module DHH.Homotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.FiniteInterval using (UnitInterval)

private
  variable
    ℓ ℓ' ℓ'' : Level
    G : Graph ℓ
    H : Graph ℓ'
    K : Graph ℓ''

-- A single time step is pointwise adjacency of graph maps.  Its proof
-- does not assert that adjacent spatial vertices remain adjacent after
-- changing both space and time at once: the cylinder uses BOX.
Step : {ℓ ℓ' : Level} {G : Graph ℓ} {H : Graph ℓ'}
       → Hom G H → Hom G H → Type (ℓ-max ℓ ℓ')
Step {G = G} {H = H} f g =
  (x : Vertex G) → Adj H (onVertices f x) (onVertices g x)

step-refl : (f : Hom G H) → Step f f
step-refl {H = H} f x = adj-refl H (onVertices f x)

step-sym : {f g : Hom G H} → Step f g → Step g f
step-sym {H = H} s x = adj-sym H (s x)

step-whisker-pre : {f g : Hom G H} → (u : Hom K G)
                 → Step f g → Step (f ∘g u) (g ∘g u)
step-whisker-pre u s x = s (onVertices u x)

step-whisker-post : {f g : Hom G H} → (u : Hom H K)
                  → Step f g → Step (u ∘g f) (u ∘g g)
step-whisker-post u s x = preserves u (s x)

-- Witnesses of finite graph homotopies.  Existence can subsequently be
-- propositionally truncated; Chain itself deliberately remembers a
-- finite sequence rather than defining the fundamental group quotient.
data Chain {ℓ ℓ'} {G : Graph ℓ} {H : Graph ℓ'}
           : Hom G H → Hom G H → Type (ℓ-max ℓ ℓ') where
  stop : (f : Hom G H) → Chain f f
  next : {f g h : Hom G H} → Step f g → Chain g h → Chain f h

chain-refl : (f : Hom G H) → Chain f f
chain-refl = stop

chain-trans : {f g h : Hom G H} → Chain f g → Chain g h → Chain f h
chain-trans (stop _) q = q
chain-trans (next s p) q = next s (chain-trans p q)

chain-sym : {f g : Hom G H} → Chain f g → Chain g f
chain-sym (stop f) = stop f
chain-sym {G = G} {H = H} (next {f = f} {g = g} s p) =
  chain-trans (chain-sym p)
    (next (step-sym {G = G} {H = H} {f = f} {g = g} s) (stop f))

chain-whisker-pre : {f g : Hom G H} → (u : Hom K G)
                   → Chain f g → Chain (f ∘g u) (g ∘g u)
chain-whisker-pre u (stop f) = stop (f ∘g u)
chain-whisker-pre {G = G} {H = H} {K = K} u (next {f = f} {g = g} s p) =
  next (step-whisker-pre {G = G} {H = H} {K = K} {f = f} {g = g} u s)
    (chain-whisker-pre u p)

chain-whisker-post : {f g : Hom G H} → (u : Hom H K)
                    → Chain f g → Chain (u ∘g f) (u ∘g g)
chain-whisker-post u (stop f) = stop (u ∘g f)
chain-whisker-post {G = G} {H = H} {K = K} u (next {f = f} {g = g} s p) =
  next (step-whisker-post {G = G} {H = H} {K = K} {f = f} {g = g} u s)
    (chain-whisker-post u p)

chain-length : {f g : Hom G H} → Chain f g → ℕ
chain-length (stop _) = zero
chain-length (next _ p) = suc (chain-length p)

-- The proposition that some finite chain exists is an equivalence
-- relation.  Truncating existence here does not truncate a realization
-- space or erase its higher paths.
Homotopic : {ℓ ℓ' : Level} {G : Graph ℓ} {H : Graph ℓ'}
            → Hom G H → Hom G H → Type (ℓ-max ℓ ℓ')
Homotopic f g = ∥ Chain f g ∥₁

homotopic-isProp : (f g : Hom G H) → isProp (Homotopic f g)
homotopic-isProp _ _ = squash₁

homotopic-refl : (f : Hom G H) → Homotopic f f
homotopic-refl f = ∣ stop f ∣₁

homotopic-sym : {f g : Hom G H} → Homotopic f g → Homotopic g f
homotopic-sym {G = G} {H = H} = PT.map (chain-sym {G = G} {H = H})

homotopic-trans : {f g h : Hom G H}
                  → Homotopic f g → Homotopic g h → Homotopic f h
homotopic-trans {G = G} {H = H} =
  PT.rec2 squash₁ (λ p q → ∣ chain-trans {G = G} {H = H} p q ∣₁)

homotopic-whisker-pre : {f g : Hom G H} → (u : Hom K G)
                       → Homotopic f g → Homotopic (f ∘g u) (g ∘g u)
homotopic-whisker-pre {G = G} {H = H} {K = K} u =
  PT.map (chain-whisker-pre {G = G} {H = H} {K = K} u)

homotopic-whisker-post : {f g : Hom G H} → (u : Hom H K)
                        → Homotopic f g → Homotopic (u ∘g f) (u ∘g g)
homotopic-whisker-post {G = G} {H = H} {K = K} u =
  PT.map (chain-whisker-post {G = G} {H = H} {K = K} u)

cylinderAt : Hom (G BOX UnitInterval) H → Bool → Hom G H
onVertices (cylinderAt c b) x = onVertices c (x , b)
preserves (cylinderAt c b) e = preserves c ∣ inr (e , refl) ∣₁

cylinderStep : (c : Hom (G BOX UnitInterval) H)
             → Step {G = G} {H = H} (cylinderAt c false) (cylinderAt c true)
cylinderStep c x = preserves c ∣ inl (refl , tt) ∣₁

stepCylinder : {f g : Hom G H} → Step f g → Hom (G BOX UnitInterval) H
stepCylinder {G = G} {H = H} {f = f} {g = g} s = record
  { onVertices = run
  ; preserves = respect
  }
  where
  run : Vertex G × Bool → Vertex H
  run (x , false) = onVertices f x
  run (x , true) = onVertices g x

  time : (x : Vertex G) (a b : Bool) → Adj H (run (x , a)) (run (x , b))
  time x false false = adj-refl H _
  time x false true = s x
  time x true false = adj-sym H (s x)
  time x true true = adj-refl H _

  space : {x y : Vertex G} → Adj G x y → (b : Bool)
         → Adj H (run (x , b)) (run (y , b))
  space e false = preserves f e
  space e true = preserves g e

  respect : {v w : Vertex G × Bool} → BoxAdj G UnitInterval v w
            → Adj H (run v) (run w)
  respect {x , a} {y , b} = PT.rec (adj-isProp H _ _) λ where
    (inl (p , _)) → subst (λ y → Adj H (run (x , a)) (run (y , b)))
                          p (time x a b)
    (inr (e , p)) → subst (λ b → Adj H (run (x , a)) (run (y , b)))
                          p (space e a)

cylinderAt-step-false : {ℓ ℓ' : Level} {G : Graph ℓ} {H : Graph ℓ'}
                       {f g : Hom G H} (s : Step {G = G} {H = H} f g)
                      → cylinderAt (stepCylinder {G = G} {H = H} {f = f} {g = g} s) false ≡ f
cylinderAt-step-false s = homExt (λ _ → refl)

cylinderAt-step-true : {ℓ ℓ' : Level} {G : Graph ℓ} {H : Graph ℓ'}
                      {f g : Hom G H} (s : Step {G = G} {H = H} f g)
                     → cylinderAt (stepCylinder {G = G} {H = H} {f = f} {g = g} s) true ≡ g
cylinderAt-step-true s = homExt (λ _ → refl)

-- In particular no separate, stronger adjacency condition is needed
-- when passing between a one-step homotopy and a graph cylinder.
cylinder-roundtrip : (c : Hom (G BOX UnitInterval) H)
                   → stepCylinder {G = G} {H = H}
                       {f = cylinderAt c false} {g = cylinderAt c true}
                       (cylinderStep {G = G} {H = H} c) ≡ c
cylinder-roundtrip c = homExt λ where
  (x , false) → refl
  (x , true) → refl
