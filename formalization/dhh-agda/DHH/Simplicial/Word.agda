{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.Word where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-suc)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ≤-sucℕ; pred-≤-pred; ¬-<-zero)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import DHH.Simplicial.Ordinal

-- Typed strings of the usual Δ generators.  Words are not morphisms:
-- different words may evaluate to the same concrete OrdinalMap.
data DeltaWord : ℕ → ℕ → Type₀ where
  idW : {n : ℕ} → DeltaWord n n
  faceW : {n : ℕ} → Fin (suc (suc n)) → DeltaWord n (suc n)
  degenW : {n : ℕ} → Fin (suc n) → DeltaWord (suc n) n
  seqW : {m n k : ℕ} → DeltaWord m n → DeltaWord n k → DeltaWord m k

evalWord : {m n : ℕ} → DeltaWord m n → OrdinalMap m n
evalWord idW = ordinalId _
evalWord (faceW i) = coface i
evalWord (degenW i) = codegeneracy i
evalWord (seqW f g) = evalWord f ⋆o evalWord g

liftOrdinal : {m n : ℕ} → OrdinalMap m n → OrdinalMap (suc m) (suc n)
mapIndex (liftOrdinal f) fzero = fzero
mapIndex (liftOrdinal f) (fsuc x) = fsuc (mapIndex f x)
monotone (liftOrdinal f) fzero y p = tt
monotone (liftOrdinal f) (fsuc x) fzero ()
monotone (liftOrdinal f) (fsuc x) (fsuc y) p = monotone f x y p

liftWord : {m n : ℕ} → DeltaWord m n → DeltaWord (suc m) (suc n)
liftWord idW = idW
liftWord (faceW i) = faceW (fsuc i)
liftWord (degenW i) = degenW (fsuc i)
liftWord (seqW f g) = seqW (liftWord f) (liftWord g)

lift-evaluation : {m n : ℕ} (w : DeltaWord m n)
                → evalWord (liftWord w) ≡ liftOrdinal (evalWord w)
lift-evaluation idW = ordinalMapExt λ where
  fzero → refl
  (fsuc x) → refl
lift-evaluation (faceW i) = ordinalMapExt λ where
  fzero → refl
  (fsuc x) → refl
lift-evaluation (degenW i) = ordinalMapExt λ where
  fzero → refl
  (fsuc x) → refl
lift-evaluation (seqW f g) =
  cong₂ _⋆o_ (lift-evaluation f) (lift-evaluation g) ∙ ordinalMapExt (λ where
    fzero → refl
    (fsuc x) → refl)

tailOrdinal : {m n : ℕ} → OrdinalMap (suc m) n → OrdinalMap m n
mapIndex (tailOrdinal f) x = mapIndex f (fsuc x)
monotone (tailOrdinal f) x y p = monotone f (fsuc x) (fsuc y) p

lowerNonzero : {n : ℕ} {a : Fin n} (b : Fin (suc n))
              → fsuc a ≤F b → Fin n
lowerNonzero fzero ()
lowerNonzero (fsuc b) p = b

lower-inverse : {n : ℕ} {a : Fin n} (b : Fin (suc n))
                (p : fsuc a ≤F b) → fsuc (lowerNonzero b p) ≡ b
lower-inverse fzero ()
lower-inverse (fsuc b) p = refl

lower-monotone : {n : ℕ} {a : Fin n} {b c : Fin (suc n)}
                 (p : fsuc a ≤F b) (q : fsuc a ≤F c)
               → b ≤F c → lowerNonzero b p ≤F lowerNonzero c q
lower-monotone {b = fzero} () q r
lower-monotone {b = fsuc b} {c = fzero} p () r
lower-monotone {b = fsuc b} {c = fsuc c} p q r = r

nonzeroEverywhere : {m n : ℕ} (f : OrdinalMap m (suc n)) (a : Fin (suc n))
                    → mapIndex f fzero ≡ fsuc a → (x : Fin (suc m))
                    → fsuc a ≤F mapIndex f x
nonzeroEverywhere f a e x = subst (λ b → b ≤F mapIndex f x) e
  (monotone f fzero x tt)

unshiftOrdinal : {m n : ℕ} (f : OrdinalMap m (suc n)) (a : Fin (suc n))
                 → mapIndex f fzero ≡ fsuc a → OrdinalMap m n
mapIndex (unshiftOrdinal f a e) x = lowerNonzero (mapIndex f x) (nonzeroEverywhere f a e x)
monotone (unshiftOrdinal f a e) x y p = lower-monotone
  {a = a} {b = mapIndex f x} {c = mapIndex f y}
  (nonzeroEverywhere f a e x) (nonzeroEverywhere f a e y) (monotone f x y p)

unshift-evaluation : {m n : ℕ} (f : OrdinalMap m (suc n)) (a : Fin (suc n))
                     (e : mapIndex f fzero ≡ fsuc a)
                   → unshiftOrdinal f a e ⋆o coface fzero ≡ f
unshift-evaluation f a e = ordinalMapExt λ x →
  lower-inverse (mapIndex f x) (nonzeroEverywhere f a e x)

duplicate-head-evaluation : {m n : ℕ} (f : OrdinalMap (suc m) n)
                           → mapIndex f fzero ≡ fzero
                           → mapIndex f (fsuc fzero) ≡ fzero
                           → codegeneracy fzero ⋆o tailOrdinal f ≡ f
duplicate-head-evaluation f e₀ e₁ = ordinalMapExt λ where
  fzero → e₁ ∙ sym e₀
  (fsuc x) → refl

prepend-head-evaluation : {m n : ℕ} (f : OrdinalMap (suc m) (suc n))
                         → mapIndex f fzero ≡ fzero
                         → (a : Fin (suc n))
                         → (e₁ : mapIndex f (fsuc fzero) ≡ fsuc a)
                         → liftOrdinal (unshiftOrdinal (tailOrdinal f) a e₁) ≡ f
prepend-head-evaluation f e₀ a e₁ = ordinalMapExt λ where
  fzero → sym e₀
  (fsuc x) → lower-inverse (mapIndex f (fsuc x))
    (nonzeroEverywhere (tailOrdinal f) a e₁ x)

singletonIndex : (x : Fin (suc zero)) → x ≡ fzero
singletonIndex fzero = refl
singletonIndex (fsuc ())

constantZeroOrdinal : (m n : ℕ) → OrdinalMap m n
mapIndex (constantZeroOrdinal m n) x = fzero
monotone (constantZeroOrdinal m n) x y p = tt

zeroTargetWord : (m : ℕ) → DeltaWord m zero
zeroTargetWord zero = idW
zeroTargetWord (suc m) = seqW (degenW fzero) (zeroTargetWord m)

zero-target-evaluation : {m : ℕ} (f : OrdinalMap m zero)
                       → evalWord (zeroTargetWord m) ≡ f
zero-target-evaluation {m = m} f = ordinalMapExt λ x →
  singletonIndex (mapIndex (evalWord (zeroTargetWord m)) x)
  ∙ sym (singletonIndex (mapIndex f x))

zero-singleton-evaluation : {n : ℕ} (f : OrdinalMap zero (suc n))
                           → mapIndex f fzero ≡ fzero
                           → constantZeroOrdinal zero n ⋆o coface (fsuc fzero) ≡ f
zero-singleton-evaluation f e = ordinalMapExt λ x →
  sym e ∙ cong (mapIndex f) (sym (singletonIndex x))

revealIndex : {m n : ℕ} (f : OrdinalMap m n) (x : Fin (suc m))
            → Σ[ y ∈ Fin (suc n) ] mapIndex f x ≡ y
revealIndex f x = mapIndex f x , refl

-- A constructive decomposition for EVERY monotone map of finite
-- nonempty ordinals into the ordinary cofaces and codegeneracies.
-- The returned equation is against the concrete map, so no unproved
-- completeness axiom for generator words is assumed.
drop-target-budget : {m n fuel : ℕ} → m + suc n ≤ suc fuel → m + n ≤ fuel
drop-target-budget {m} {n} {fuel} p = pred-≤-pred (subst (_≤ suc fuel) (+-suc m n) p)

drop-source-budget : {m n fuel : ℕ} → suc m + n ≤ suc fuel → m + n ≤ fuel
drop-source-budget p = pred-≤-pred p

smaller-target-budget : {m n fuel : ℕ} → m + suc n ≤ fuel → m + n ≤ fuel
smaller-target-budget {m} {n} p = ≤-trans
  (subst ((m + n) ≤_) (sym (+-suc m n)) ≤-sucℕ) p

-- Structural fuel is bounded below by m+n.  This makes termination
-- explicit even when pattern matching reveals finite-index values.
normalizeFuel : (fuel : ℕ) {m n : ℕ} → m + n ≤ fuel → (f : OrdinalMap m n)
                → Σ[ w ∈ DeltaWord m n ] evalWord w ≡ f
normalizeFuel fuel {m = m} {n = zero} budget f = zeroTargetWord m , zero-target-evaluation f
normalizeFuel zero {m = m} {n = suc n} budget f =
  Empty.rec (¬-<-zero (subst (_≤ zero) (+-suc m n) budget))
normalizeFuel (suc fuel) {m = zero} {n = suc n} budget f with revealIndex f fzero
... | fzero , e =
  let w , q = normalizeFuel fuel (drop-target-budget {m = zero} {n = n} budget) (constantZeroOrdinal zero n)
  in seqW w (faceW (fsuc fzero)) ,
    cong (λ h → h ⋆o coface (fsuc fzero)) q ∙ zero-singleton-evaluation f e
... | fsuc a , e =
  let w , q = normalizeFuel fuel (drop-target-budget {m = zero} {n = n} budget) (unshiftOrdinal f a e)
  in seqW w (faceW fzero) ,
    cong (λ h → h ⋆o coface fzero) q ∙ unshift-evaluation f a e
normalizeFuel (suc fuel) {m = suc m} {n = suc n} budget f
  with revealIndex f fzero | revealIndex f (fsuc fzero)
... | fzero , e₀ | fzero , e₁ =
  let w , q = normalizeFuel fuel (drop-source-budget {m = m} {n = suc n} budget) (tailOrdinal f)
  in seqW (degenW fzero) w ,
    cong (λ h → codegeneracy fzero ⋆o h) q ∙ duplicate-head-evaluation f e₀ e₁
... | fzero , e₀ | fsuc a , e₁ =
  let w , q = normalizeFuel fuel (smaller-target-budget {m = m} {n = n}
                (drop-source-budget {m = m} {n = suc n} budget))
                (unshiftOrdinal (tailOrdinal f) a e₁)
  in liftWord w , lift-evaluation w ∙ cong liftOrdinal q ∙ prepend-head-evaluation f e₀ a e₁
... | fsuc a , e₀ | b , e₁ =
  let w , q = normalizeFuel fuel (drop-target-budget {m = suc m} {n = n} budget) (unshiftOrdinal f a e₀)
  in seqW w (faceW fzero) ,
    cong (λ h → h ⋆o coface fzero) q ∙ unshift-evaluation f a e₀

normalizeOrdinal : {m n : ℕ} (f : OrdinalMap m n)
                 → Σ[ w ∈ DeltaWord m n ] evalWord w ≡ f
normalizeOrdinal {m = m} {n = n} = normalizeFuel (m + n) ≤-refl
