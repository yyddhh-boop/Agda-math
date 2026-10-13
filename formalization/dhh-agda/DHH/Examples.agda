{-# OPTIONS --cubical --safe #-}

module DHH.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; false; true; false≢true; true≢false)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.FiniteInterval
open import DHH.Homotopy
open import DHH.Cellular2
import DHH.BoundaryChecks as BC

-- The reflexive four-cycle.  The four vertices in cyclic order are
-- a=(0,0), b=(1,0), c=(1,1), d=(0,1); diagonals are absent.
C4 : Graph ℓ-zero
C4 = UnitInterval BOX UnitInterval

a b c d : Vertex C4
a = false , false
b = true , false
c = true , true
d = false , true

ab : Adj C4 a b
ab = ∣ inr (tt , refl) ∣₁

bc : Adj C4 b c
bc = ∣ inl (refl , tt) ∣₁

ad : Adj C4 a d
ad = ∣ inl (refl , tt) ∣₁

dc : Adj C4 d c
dc = ∣ inr (tt , refl) ∣₁

b-not-adjacent-d : Adj C4 b d → ⊥
b-not-adjacent-d = PT.rec isProp⊥ λ where
  (inl (p , _)) → true≢false p
  (inr (_ , p)) → false≢true p

-- An actual square exists because precisely its four side edges exist.
c4Square : GraphSquare C4
c4Square = record
  { v00 = a ; v10 = b ; v01 = d ; v11 = c
  ; bottom = ab ; top = dc ; left = ad ; right = bc
  }

-- In the auxiliary HIT Cell₂, the square supplies a two-dimensional
-- equality between the two routes.  This is not yet a theorem about
-- the complete geometric realization |N₁C4|.
c4-routes-agree : edge ab ∙ edge bc ≡ edge ad ∙ edge dc
c4-routes-agree = routesAgree c4Square

-- Graph contraction: (a,b,c,d) -> (a,b,b,a) -> (a,a,a,a).
foldC4 : Hom C4 C4
onVertices foldC4 (x , _) = x , false
preserves foldC4 = PT.rec (adj-isProp C4 _ _) λ where
  (inl (p , _)) → ∣ inl (p , tt) ∣₁
  (inr (_ , _)) → ∣ inr (tt , refl) ∣₁

id-to-fold : Step {G = C4} {H = C4} (idHom C4) foldC4
id-to-fold (x , y) = ∣ inl (refl , tt) ∣₁

fold-to-constant : Step {G = C4} {H = C4} foldC4 (constantHom C4 a)
fold-to-constant (x , y) = ∣ inr (tt , refl) ∣₁

c4-contracts : Chain (idHom C4) (constantHom C4 a)
c4-contracts = next {g = foldC4} id-to-fold
  (next {g = constantHom C4 a} fold-to-constant (stop (constantHom C4 a)))

c4-contraction-has-two-steps : chain-length {G = C4} {H = C4} c4-contracts ≡ 2
c4-contraction-has-two-steps = refl

-- The endpoint-fixed two-row grid from the visual explanation.
upperRow : Hom I3 C4
upperRow = path3 C4 a a b c (adj-refl C4 a) ab bc

lowerRow : Hom I3 C4
lowerRow = path3 C4 a d c c ad dc (adj-refl C4 c)

upperRow-to-lowerRow : Step {G = I3} {H = C4} upperRow lowerRow
upperRow-to-lowerRow p0 = adj-refl C4 a
upperRow-to-lowerRow p1 = ad
upperRow-to-lowerRow p2 = bc
upperRow-to-lowerRow p3 = adj-refl C4 c

twoRowGrid : Hom (I3 BOX UnitInterval) C4
twoRowGrid = stepCylinder {G = I3} {H = C4} {f = upperRow} {g = lowerRow} upperRow-to-lowerRow

grid-start-fixed : (t : Bool) → onVertices twoRowGrid (p0 , t) ≡ a
grid-start-fixed false = refl
grid-start-fixed true = refl

grid-end-fixed : (t : Bool) → onVertices twoRowGrid (p3 , t) ≡ c
grid-end-fixed false = refl
grid-end-fixed true = refl

-- Reuse the three-vertex path already defined for the boundary checks.
shortVia : (middle : Vertex C4) → Adj C4 a middle → Adj C4 middle c
           → Hom BC.ThreePath C4
shortVia middle e01 e12 = record
  { onVertices = run ; preserves = respect }
  where
  run : BC.Three → Vertex C4
  run BC.zero = a
  run BC.one = middle
  run BC.two = c
  respect : {x y : BC.Three} → BC.PathAdj x y → Adj C4 (run x) (run y)
  respect {BC.zero} {BC.zero} _ = adj-refl C4 a
  respect {BC.zero} {BC.one} _ = e01
  respect {BC.zero} {BC.two} ()
  respect {BC.one} {BC.zero} _ = adj-sym C4 e01
  respect {BC.one} {BC.one} _ = adj-refl C4 middle
  respect {BC.one} {BC.two} _ = e12
  respect {BC.two} {BC.zero} ()
  respect {BC.two} {BC.one} _ = adj-sym C4 e12
  respect {BC.two} {BC.two} _ = adj-refl C4 c

shortUpper : Hom BC.ThreePath C4
shortUpper = shortVia b ab bc

shortLower : Hom BC.ThreePath C4
shortLower = shortVia d ad dc

-- (a,b,c) and (a,d,c) cannot be one-step homotopic with their
-- current shared parametrization: its middle time edge would be b--d.
short-paths-not-one-step : Step {G = BC.ThreePath} {H = C4} shortUpper shortLower → ⊥
short-paths-not-one-step s = b-not-adjacent-d (s BC.one)
