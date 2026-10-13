{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.Ordinal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; isSetFin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)

-- Finite ordinals, with proposition-valued numerical order.
infix 4 _≤F_
_≤F_ : {m n : ℕ} → Fin m → Fin n → Type₀
fzero ≤F y = Unit
fsuc x ≤F fzero = ⊥
fsuc x ≤F fsuc y = x ≤F y

≤F-isProp : {m n : ℕ} (x : Fin m) (y : Fin n) → isProp (x ≤F y)
≤F-isProp fzero y = isPropUnit
≤F-isProp (fsuc x) fzero = isProp⊥
≤F-isProp (fsuc x) (fsuc y) = ≤F-isProp x y

≤F-refl : {n : ℕ} (x : Fin n) → x ≤F x
≤F-refl fzero = tt
≤F-refl (fsuc x) = ≤F-refl x

≤F-trans : {l m n : ℕ} {x : Fin l} {y : Fin m} {z : Fin n}
         → x ≤F y → y ≤F z → x ≤F z
≤F-trans {x = fzero} p q = tt
≤F-trans {x = fsuc x} {y = fzero} () q
≤F-trans {x = fsuc x} {y = fsuc y} {z = fzero} p ()
≤F-trans {x = fsuc x} {y = fsuc y} {z = fsuc z} p q = ≤F-trans {x = x} {y} {z} p q

Monotone : {m n : ℕ} → (Fin m → Fin n) → Type₀
Monotone f = (x y : _) → x ≤F y → f x ≤F f y

monotone-isProp : {m n : ℕ} (f : Fin m → Fin n) → isProp (Monotone f)
monotone-isProp f = isPropΠ3 (λ x y _ → ≤F-isProp (f x) (f y))

-- Object n means the nonempty ordinal [n] = {0,...,n}.
record OrdinalMap (m n : ℕ) : Type₀ where
  constructor ordinalMap
  field
    mapIndex : Fin (suc m) → Fin (suc n)
    monotone : Monotone mapIndex
open OrdinalMap public

ordinalId : (n : ℕ) → OrdinalMap n n
mapIndex (ordinalId n) x = x
monotone (ordinalId n) x y p = p

infixl 20 _⋆o_
_⋆o_ : {m n k : ℕ} → OrdinalMap m n → OrdinalMap n k → OrdinalMap m k
mapIndex (f ⋆o g) x = mapIndex g (mapIndex f x)
monotone (f ⋆o g) x y p = monotone g _ _ (monotone f x y p)

ordinalMapExt : {m n : ℕ} {f g : OrdinalMap m n}
              → ((x : Fin (suc m)) → mapIndex f x ≡ mapIndex g x) → f ≡ g
mapIndex (ordinalMapExt p i) x = p x i
monotone (ordinalMapExt {f = f} {g = g} p i) x y e =
  isProp→PathP
    {B = λ j → p x j ≤F p y j}
    (λ j → ≤F-isProp (p x j) (p y j))
    (monotone f x y e) (monotone g x y e) i

ordinalToΣ : {m n : ℕ} → OrdinalMap m n
            → Σ (Fin (suc m) → Fin (suc n)) Monotone
ordinalToΣ f = mapIndex f , monotone f

ΣToOrdinal : {m n : ℕ} → Σ (Fin (suc m) → Fin (suc n)) Monotone → OrdinalMap m n
ΣToOrdinal (f , p) = ordinalMap f p

isSetOrdinalMap : {m n : ℕ} → isSet (OrdinalMap m n)
isSetOrdinalMap = isSetRetract ordinalToΣ ΣToOrdinal
  (λ f → ordinalMapExt (λ _ → refl))
  (isSetΣSndProp (isSetΠ (λ _ → isSetFin)) monotone-isProp)

Delta : Category ℓ-zero ℓ-zero
Category.ob Delta = ℕ
Category.Hom[_,_] Delta = OrdinalMap
Category.id Delta {x = n} = ordinalId n
Category._⋆_ Delta = _⋆o_
Category.⋆IdL Delta f = ordinalMapExt (λ _ → refl)
Category.⋆IdR Delta f = ordinalMapExt (λ _ → refl)
Category.⋆Assoc Delta f g h = ordinalMapExt (λ _ → refl)
Category.isSetHom Delta = isSetOrdinalMap

-- Injection skipping a specified vertex.  The following recursion
-- also works before packaging it as a nonempty ordinal map.
skip : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
skip fzero x = fsuc x
skip (fsuc i) fzero = fzero
skip (fsuc i) (fsuc x) = fsuc (skip i x)

skip-monotone : {n : ℕ} (i : Fin (suc n)) → Monotone (skip i)
skip-monotone fzero x y e = e
skip-monotone (fsuc i) fzero y e = tt
skip-monotone (fsuc i) (fsuc x) fzero ()
skip-monotone (fsuc i) (fsuc x) (fsuc y) e = skip-monotone i x y e

coface : {n : ℕ} → Fin (suc (suc n)) → OrdinalMap n (suc n)
mapIndex (coface i) = skip i
monotone (coface i) = skip-monotone i

-- The same operation with an arbitrary target cardinality, including
-- the empty case (where no index can be supplied).
collapseAny : {n : ℕ} → Fin n → Fin (suc n) → Fin n
collapseAny fzero fzero = fzero
collapseAny fzero (fsuc x) = x
collapseAny (fsuc i) fzero = fzero
collapseAny (fsuc i) (fsuc x) = fsuc (collapseAny i x)

-- Surjection identifying vertices i and i+1.
collapse : {n : ℕ} → Fin (suc n) → Fin (suc (suc n)) → Fin (suc n)
collapse = collapseAny

collapse-monotone : {n : ℕ} (i : Fin (suc n)) → Monotone (collapse i)
collapse-monotone fzero fzero y e = tt
collapse-monotone fzero (fsuc x) fzero ()
collapse-monotone fzero (fsuc x) (fsuc y) e = e
collapse-monotone {n = zero} (fsuc ()) x y e
collapse-monotone {n = suc n} (fsuc i) fzero y e = tt
collapse-monotone {n = suc n} (fsuc i) (fsuc x) fzero ()
collapse-monotone {n = suc n} (fsuc i) (fsuc x) (fsuc y) e = collapse-monotone i x y e

codegeneracy : {n : ℕ} → Fin (suc n) → OrdinalMap (suc n) n
mapIndex (codegeneracy i) = collapse i
monotone (codegeneracy i) = collapse-monotone i
