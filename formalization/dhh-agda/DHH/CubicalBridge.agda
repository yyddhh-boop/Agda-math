{-# OPTIONS --cubical --safe #-}

module DHH.CubicalBridge where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.Cubes using (Q; Cube)
open import DHH.Cellular2

private
  variable
    ℓ : Level

cubeToSquare : {G : Graph ℓ} → Cube G 2 → GraphSquare G
v00 (cubeToSquare c) = onVertices c (false , (false , tt))
v10 (cubeToSquare c) = onVertices c (true  , (false , tt))
v01 (cubeToSquare c) = onVertices c (false , (true  , tt))
v11 (cubeToSquare c) = onVertices c (true  , (true  , tt))
bottom (cubeToSquare c) = preserves c ∣ inr (tt , refl) ∣₁
top    (cubeToSquare c) = preserves c ∣ inr (tt , refl) ∣₁
left   (cubeToSquare c) = preserves c ∣ inl (refl , ∣ inr (tt , refl) ∣₁) ∣₁
right  (cubeToSquare c) = preserves c ∣ inl (refl , ∣ inr (tt , refl) ∣₁) ∣₁

squareVertex : {G : Graph ℓ} → GraphSquare G → Bool → Bool → Vertex G
squareVertex s false false = v00 s
squareVertex s true  false = v10 s
squareVertex s false true  = v01 s
squareVertex s true  true  = v11 s

horizontal : {G : Graph ℓ} (s : GraphSquare G) (x x' y : Bool)
           → Adj G (squareVertex s x y) (squareVertex s x' y)
horizontal {G = G} s false false false = adj-refl G (v00 s)
horizontal {G = G} s true  true  false = adj-refl G (v10 s)
horizontal {G = G} s false false true  = adj-refl G (v01 s)
horizontal {G = G} s true  true  true  = adj-refl G (v11 s)
horizontal s false true  false = bottom s
horizontal s false true  true  = top s
horizontal {G = G} s true false false = adj-sym G (bottom s)
horizontal {G = G} s true false true  = adj-sym G (top s)

vertical : {G : Graph ℓ} (s : GraphSquare G) (x y y' : Bool)
         → Adj G (squareVertex s x y) (squareVertex s x y')
vertical {G = G} s false false false = adj-refl G (v00 s)
vertical {G = G} s true  false false = adj-refl G (v10 s)
vertical {G = G} s false true  true  = adj-refl G (v01 s)
vertical {G = G} s true  true  true  = adj-refl G (v11 s)
vertical s false false true = left s
vertical s true  false true = right s
vertical {G = G} s false true false = adj-sym G (left s)
vertical {G = G} s true  true false = adj-sym G (right s)

squareToCube : {G : Graph ℓ} → GraphSquare G → Cube G 2
onVertices (squareToCube s) (x , (y , tt)) = squareVertex s x y
preserves (squareToCube {G = G} s)
          {x = (x , (y , tt))} {y = (x' , (y' , tt))} =
  PT.rec (adj-isProp G _ _) λ where
    (inl (p , e)) →
      subst (λ z → Adj G (squareVertex s x y) (squareVertex s z y'))
            p (vertical s x y y')
    (inr (e , p)) →
      subst (λ z → Adj G (squareVertex s x y) (squareVertex s x' z))
            (cong fst p) (horizontal s x x' y)

cubeRoundTrip : {G : Graph ℓ} (c : Cube G 2)
              → squareToCube (cubeToSquare c) ≡ c
cubeRoundTrip c = homExt λ where
  (false , (false , tt)) → refl
  (false , (true  , tt)) → refl
  (true  , (false , tt)) → refl
  (true  , (true  , tt)) → refl

squareRoundTrip : {G : Graph ℓ} (s : GraphSquare G)
                → cubeToSquare (squareToCube s) ≡ s
v00 (squareRoundTrip s i) = v00 s
v10 (squareRoundTrip s i) = v10 s
v01 (squareRoundTrip s i) = v01 s
v11 (squareRoundTrip s i) = v11 s
bottom (squareRoundTrip {G = G} s i) =
  adj-isProp G _ _ (bottom (cubeToSquare (squareToCube s))) (bottom s) i
top (squareRoundTrip {G = G} s i) =
  adj-isProp G _ _ (top (cubeToSquare (squareToCube s))) (top s) i
left (squareRoundTrip {G = G} s i) =
  adj-isProp G _ _ (left (cubeToSquare (squareToCube s))) (left s) i
right (squareRoundTrip {G = G} s i) =
  adj-isProp G _ _ (right (cubeToSquare (squareToCube s))) (right s) i

cubeSquareIso : {G : Graph ℓ} → Iso (Cube G 2) (GraphSquare G)
cubeSquareIso = iso cubeToSquare squareToCube squareRoundTrip cubeRoundTrip

-- This conclusion lives in the explicitly defined auxiliary HIT.
-- An identification with the full nerve realization remains to be proved.
cubeRoutesAgree : {G : Graph ℓ} (c : Cube G 2)
                → edge (bottom (cubeToSquare c)) ∙ edge (right (cubeToSquare c))
                ≡ edge (left (cubeToSquare c)) ∙ edge (top (cubeToSquare c))
cubeRoutesAgree c = routesAgree (cubeToSquare c)
