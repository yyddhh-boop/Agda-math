{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.UnitComparison where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Categories.NaturalTransformation.Base using (NatTrans)
open import DHH.Graph
open import DHH.FiniteInterval using (UnitInterval)
open import DHH.Cubes using (PointGraph; Q; boxHom)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.StableNerve.Interval
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Colimit

private variable ℓ ℓ' : Level

fromBool : Bool → Fin 2
fromBool false = fzero
fromBool true = fsuc fzero

toBool-from : (b : Bool) → threshold fzero (fromBool b) ≡ b
toBool-from false = refl
toBool-from true = refl
fromBool-to : (a : Fin 2) → fromBool (threshold fzero a) ≡ a
fromBool-to fzero = refl
fromBool-to (fsuc fzero) = refl

fromUnitInterval : Hom UnitInterval (Iₘ 1)
onVertices fromUnitInterval = fromBool
preserves fromUnitInterval {x = false} {y = false} e = tt
preserves fromUnitInterval {x = false} {y = true} e = tt
preserves fromUnitInterval {x = true} {y = false} e = tt
preserves fromUnitInterval {x = true} {y = true} e = tt

toUnitInterval : Hom (Iₘ 1) UnitInterval
onVertices toUnitInterval = threshold fzero
preserves toUnitInterval e = tt

toUnit : (n : ℕ) → Hom (Grid 1 n) (Q n)
onVertices (toUnit n) = thresholdGrid fzero n
preserves (toUnit zero) e = tt
preserves (toUnit (suc n)) e = preserves (boxHom toUnitInterval (toUnit n)) e

fromUnit : (n : ℕ) → Hom (Q n) (Grid 1 n)
fromUnit zero = idHom PointGraph
fromUnit (suc n) = boxHom fromUnitInterval (fromUnit n)

to-from : (n : ℕ) (x : Vertex (Q n)) → onVertices (toUnit n) (onVertices (fromUnit n) x) ≡ x
to-from zero x = refl
to-from (suc n) (b , x) = cong₂ _,_ (toBool-from b) (to-from n x)
from-to : (n : ℕ) (x : Vertex (Grid 1 n)) → onVertices (fromUnit n) (onVertices (toUnit n) x) ≡ x
from-to zero x = refl
from-to (suc n) (a , x) = cong₂ _,_ (fromBool-to a) (from-to n x)

fromUnit-natural : {m n : ℕ} (u : CubicalMap m n) (x : Vertex (Q m))
  → onVertices (gridAction 1 u) (onVertices (fromUnit m) x)
    ≡ onVertices (fromUnit n) (onVertices (underlying u) x)
fromUnit-natural {m} {n} u x =
  sym (from-to n (onVertices (gridAction 1 u) (onVertices (fromUnit m) x)))
  ∙ cong (onVertices (fromUnit n))
      (gridAction-threshold 1 u fzero (onVertices (fromUnit m) x)
       ∙ cong (onVertices (underlying u)) (to-from m x))

unitToGrid : (G : Graph ℓ) → CubicalNatural (N₁ G) (Nₘ 1 G)
mapCells (unitToGrid G) n c = c ∘g toUnit n
natural (unitToGrid G) {m} {n} u c = homExt λ x →
  cong (onVertices c) (sym (gridAction-threshold 1 u fzero x))

gridToUnit : (G : Graph ℓ) → CubicalNatural (Nₘ 1 G) (N₁ G)
mapCells (gridToUnit G) n c = c ∘g fromUnit n
natural (gridToUnit G) {m} {n} u c = homExt λ x → cong (onVertices c) (fromUnit-natural u x)

unit-grid-unit : (G : Graph ℓ) → unitToGrid G ⋆n gridToUnit G ≡ cubicalId (N₁ G)
unit-grid-unit G = cubicalNaturalExt λ n c → homExt λ x → cong (onVertices c) (to-from n x)
grid-unit-grid : (G : Graph ℓ) → gridToUnit G ⋆n unitToGrid G ≡ cubicalId (Nₘ 1 G)
grid-unit-grid G = cubicalNaturalExt λ n c → homExt λ x → cong (onVertices c) (from-to n x)

-- The original Boolean-cube N₁ comparison, constructed through an
-- actual natural isomorphism of the two unit-grid encodings.
N₁-to-N∞ : (G : Graph ℓ) → CubicalNatural (N₁ G) (N∞ G)
N₁-to-N∞ G = unitToGrid G ⋆n includeStage G zero

N₁-to-N∞-natural : {G : Graph ℓ} {H : Graph ℓ'} (f : Hom G H)
  → N₁-to-N∞ G ⋆n N∞-map f ≡ N₁-map f ⋆n N₁-to-N∞ H
N₁-to-N∞-natural {H = H} f = cubicalNaturalExt λ n c →
  cong (λ d → Stable.point H n (zero , d)) (homExt (λ _ → refl))

N₁-to-N∞-transformation : (ℓ : Level) → NatTrans (N₁-functor ℓ) (N∞-functor ℓ)
NatTrans.N-ob (N₁-to-N∞-transformation ℓ) = N₁-to-N∞
NatTrans.N-hom (N₁-to-N∞-transformation ℓ) f = sym (N₁-to-N∞-natural f)
