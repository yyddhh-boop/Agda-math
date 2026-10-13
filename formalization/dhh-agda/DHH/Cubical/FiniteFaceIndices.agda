{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.FiniteFaceIndices where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (equivToIso)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import Cubical.Data.FinData using (Fin; discreteFin)
  renaming (zero to fzero; suc to fsuc)
import Cubical.Data.FinData.Properties as FData
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr; ⊎Iso)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete; ¬_)
open import DHH.Cubes using
  (Position; here; there; CoordinatePair; front; under; lower; upper; lowerWide; upperWide)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.FaceIntersections using
  (PairwiseFaceData; faceCells; pairwiseAgreement; cube-faces-commute)

private variable ℓ : Level

-- 枚举同时带双向算法和两逆证明；有限性不是一个需再选择代表的截断。
record Enumeration (A : Type₀) : Type₀ where
  field
    count : ℕ
    indexing : Iso (Fin count) A
open Enumeration public

enumerate : {A : Type₀} (E : Enumeration A) → Fin (count E) → A
enumerate E = Iso.fun (indexing E)

number : {A : Type₀} (E : Enumeration A) → A → Fin (count E)
number E = Iso.inv (indexing E)

enumerate-number : {A : Type₀} (E : Enumeration A) (a : A) → enumerate E (number E a) ≡ a
enumerate-number E = Iso.rightInv (indexing E)

number-enumerate : {A : Type₀} (E : Enumeration A) (i : Fin (count E)) → number E (enumerate E i) ≡ i
number-enumerate E = Iso.leftInv (indexing E)

mapEnumeration : {A B : Type₀} → Iso A B → Enumeration A → Enumeration B
count (mapEnumeration f E) = count E
indexing (mapEnumeration f E) = compIso (indexing E) f

emptyEnumeration : Enumeration ⊥
count emptyEnumeration = zero
Iso.fun (indexing emptyEnumeration) ()
Iso.inv (indexing emptyEnumeration) ()
Iso.rightInv (indexing emptyEnumeration) ()
Iso.leftInv (indexing emptyEnumeration) ()

boolEnumeration : Enumeration Bool
count boolEnumeration = suc (suc zero)
Iso.fun (indexing boolEnumeration) fzero = false
Iso.fun (indexing boolEnumeration) (fsuc fzero) = true
Iso.inv (indexing boolEnumeration) false = fzero
Iso.inv (indexing boolEnumeration) true = fsuc fzero
Iso.rightInv (indexing boolEnumeration) false = refl
Iso.rightInv (indexing boolEnumeration) true = refl
Iso.leftInv (indexing boolEnumeration) fzero = refl
Iso.leftInv (indexing boolEnumeration) (fsuc fzero) = refl

positionFromFin : {n : ℕ} → Fin n → Position n
positionFromFin fzero = here
positionFromFin (fsuc i) = there (positionFromFin i)

positionToFin : {n : ℕ} → Position n → Fin n
positionToFin here = fzero
positionToFin (there i) = fsuc (positionToFin i)

position-right : {n : ℕ} (i : Position n) → positionFromFin (positionToFin i) ≡ i
position-right here = refl
position-right (there i) = cong there (position-right i)

position-left : {n : ℕ} (i : Fin n) → positionToFin (positionFromFin i) ≡ i
position-left fzero = refl
position-left (fsuc i) = cong fsuc (position-left i)

positionEnumeration : (n : ℕ) → Enumeration (Position n)
count (positionEnumeration n) = n
indexing (positionEnumeration n) = iso positionFromFin positionToFin position-right position-left

sumEnumeration : {A B : Type₀} → Enumeration A → Enumeration B → Enumeration (A ⊎ B)
count (sumEnumeration E F) = count E + count F
indexing (sumEnumeration E F) = compIso
  (invIso (equivToIso (FData.FinSumChar.Equiv (count E) (count F))))
  (⊎Iso (indexing E) (indexing F))

productEnumeration : {A B : Type₀} → Enumeration A → Enumeration B → Enumeration (A × B)
count (productEnumeration E F) = count E · count F
indexing (productEnumeration E F) = compIso
  (invIso (equivToIso (FData.FinProdChar.Equiv (count E) (count F))))
  (prodIso (indexing E) (indexing F))

coordinateSplit : (n : ℕ) → Iso (CoordinatePair (suc n))
  (Position (suc (suc n)) ⊎ CoordinatePair n)
Iso.fun (coordinateSplit n) (front i) = inl i
Iso.fun (coordinateSplit n) (under p) = inr p
Iso.inv (coordinateSplit n) (inl i) = front i
Iso.inv (coordinateSplit n) (inr p) = under p
Iso.rightInv (coordinateSplit n) (inl i) = refl
Iso.rightInv (coordinateSplit n) (inr p) = refl
Iso.leftInv (coordinateSplit n) (front i) = refl
Iso.leftInv (coordinateSplit n) (under p) = refl

-- front 枚举第一个坐标与后面各坐标；under 递归枚举公共前缀之后
-- 的坐标对。每对不同坐标恰出现一次，两逆证明保证没有遗漏。
coordinateEnumeration : (n : ℕ) → Enumeration (CoordinatePair n)
count (coordinateEnumeration zero) = suc zero
Iso.fun (indexing (coordinateEnumeration zero)) fzero = front here
Iso.inv (indexing (coordinateEnumeration zero)) (front here) = fzero
Iso.rightInv (indexing (coordinateEnumeration zero)) (front here) = refl
Iso.leftInv (indexing (coordinateEnumeration zero)) fzero = refl
coordinateEnumeration (suc n) = mapEnumeration (invIso (coordinateSplit n))
  (sumEnumeration (positionEnumeration (suc (suc n))) (coordinateEnumeration n))

facetEnumeration : (n : ℕ) → Enumeration (Facet n)
facetEnumeration n = productEnumeration (positionEnumeration (suc n)) boolEnumeration

discreteEnumeration : {A : Type₀} → Enumeration A → Discrete A
discreteEnumeration E a b with discreteFin (number E a) (number E b)
... | yes p = yes (sym (enumerate-number E a) ∙ cong (enumerate E) p ∙ enumerate-number E b)
... | no q = no (λ p → q (cong (number E) p))

-- 对 Fin 的长度递归过滤。yes 分支保留首项，no 分支丢弃首项。
-- 尾部每次缩短，所得 count 和索引都是实际有限算法。
filterFin : (r : ℕ) (P : Fin r → Type₀)
  → ((i : Fin r) → isProp (P i)) → ((i : Fin r) → Dec (P i))
  → Enumeration (Σ[ i ∈ Fin r ] P i)
count (filterFin zero P prop dec) = zero
Iso.fun (indexing (filterFin zero P prop dec)) ()
Iso.inv (indexing (filterFin zero P prop dec)) (() , p)
Iso.rightInv (indexing (filterFin zero P prop dec)) (() , p)
Iso.leftInv (indexing (filterFin zero P prop dec)) ()
filterFin (suc r) P prop dec with dec fzero
... | yes head = result
  where
  tail = filterFin r (λ i → P (fsuc i)) (λ i → prop (fsuc i)) (λ i → dec (fsuc i))
  raise : (Σ[ i ∈ Fin r ] P (fsuc i)) → Σ[ i ∈ Fin (suc r) ] P i
  raise (i , p) = fsuc i , p
  result : Enumeration (Σ[ i ∈ Fin (suc r) ] P i)
  count result = suc (count tail)
  Iso.fun (indexing result) fzero = fzero , head
  Iso.fun (indexing result) (fsuc i) = raise (enumerate tail i)
  Iso.inv (indexing result) (fzero , p) = fzero
  Iso.inv (indexing result) (fsuc i , p) = fsuc (number tail (i , p))
  Iso.rightInv (indexing result) (fzero , p) = Σ≡Prop prop refl
  Iso.rightInv (indexing result) (fsuc i , p) = cong raise (enumerate-number tail (i , p))
  Iso.leftInv (indexing result) fzero = refl
  Iso.leftInv (indexing result) (fsuc i) = cong fsuc (number-enumerate tail i)
... | no head = result
  where
  tail = filterFin r (λ i → P (fsuc i)) (λ i → prop (fsuc i)) (λ i → dec (fsuc i))
  raise : (Σ[ i ∈ Fin r ] P (fsuc i)) → Σ[ i ∈ Fin (suc r) ] P i
  raise (i , p) = fsuc i , p
  result : Enumeration (Σ[ i ∈ Fin (suc r) ] P i)
  count result = count tail
  Iso.fun (indexing result) i = raise (enumerate tail i)
  Iso.inv (indexing result) (fzero , p) = rec (head p)
  Iso.inv (indexing result) (fsuc i , p) = number tail (i , p)
  Iso.rightInv (indexing result) (fzero , p) = rec (head p)
  Iso.rightInv (indexing result) (fsuc i , p) = cong raise (enumerate-number tail (i , p))
  Iso.leftInv (indexing result) i = number-enumerate tail i

filterEnumeration : {A : Type₀} (E : Enumeration A) (P : A → Type₀)
  → ((a : A) → isProp (P a)) → ((a : A) → Dec (P a))
  → Enumeration (Σ[ a ∈ A ] P a)
filterEnumeration E P prop dec = mapEnumeration
  (Σ-cong-iso-fst (indexing E))
  (filterFin (count E) (λ i → P (enumerate E i))
    (λ i → prop (enumerate E i)) (λ i → dec (enumerate E i)))

SelectedFacet : {n : ℕ} → FaceSelection n → Type₀
SelectedFacet {n} S = Σ[ j ∈ Facet n ] fst (S j)

DecSelection : {n : ℕ} → FaceSelection n → Type₀
DecSelection {n} S = (j : Facet n) → Dec (fst (S j))

selectedFacetEnumeration : {n : ℕ} (S : FaceSelection n)
  → DecSelection S → Enumeration (SelectedFacet S)
selectedFacetEnumeration {n} S dec = filterEnumeration (facetEnumeration n)
  (λ j → fst (S j)) (λ j → snd (S j)) dec

RawCodim2 : ℕ → Type₀
RawCodim2 zero = ⊥
RawCodim2 (suc n) = CoordinatePair n × (Bool × Bool)

intersectionDimension : ℕ → ℕ
intersectionDimension zero = zero
intersectionDimension (suc n) = n

lowerFacet upperFacet : {n : ℕ} → RawCodim2 n → Facet n
lowerFacet {n = zero} ()
lowerFacet {n = suc n} (r , a , b) = lowerWide r , a
upperFacet {n = zero} ()
upperFacet {n = suc n} (r , a , b) = upperWide r , b

lowerOverlap upperOverlap : {n : ℕ} → RawCodim2 n
  → CubicalMap (intersectionDimension n) n
lowerOverlap {n = zero} ()
lowerOverlap {n = suc n} (r , a , b) = cubeFace (upper r) b
upperOverlap {n = zero} ()
upperOverlap {n = suc n} (r , a , b) = cubeFace (lower r) a

overlap-square : {n : ℕ} (r : RawCodim2 n)
  → lowerOverlap r ⋆c facetMap (lowerFacet r) ≡ upperOverlap r ⋆c facetMap (upperFacet r)
overlap-square {n = zero} ()
overlap-square {n = suc n} (r , a , b) = cube-faces-commute r a b

rawCodim2Enumeration : (n : ℕ) → Enumeration (RawCodim2 n)
rawCodim2Enumeration zero = emptyEnumeration
rawCodim2Enumeration (suc n) = productEnumeration (coordinateEnumeration n)
  (productEnumeration boolEnumeration boolEnumeration)

SelectedCodim2 : {n : ℕ} → FaceSelection n → Type₀
SelectedCodim2 {n} S = Σ[ r ∈ RawCodim2 n ]
  (fst (S (lowerFacet r)) × fst (S (upperFacet r)))

decProduct : {A B : Type₀} → Dec A → Dec B → Dec (A × B)
decProduct (yes a) (yes b) = yes (a , b)
decProduct (no a) _ = no (λ p → a (fst p))
decProduct (yes a) (no b) = no (λ p → b (snd p))

selectedCodim2Enumeration : {n : ℕ} (S : FaceSelection n)
  → DecSelection S → Enumeration (SelectedCodim2 S)
selectedCodim2Enumeration {n} S dec = filterEnumeration (rawCodim2Enumeration n)
  (λ r → fst (S (lowerFacet r)) × fst (S (upperFacet r)))
  (λ r → isProp× (snd (S (lowerFacet r))) (snd (S (upperFacet r))))
  (λ r → decProduct (dec (lowerFacet r)) (dec (upperFacet r)))

boundaryDecision : (n : ℕ) → DecSelection (allFaces n)
boundaryDecision n j = yes tt

openBoxDecision : {n : ℕ} (missing : Facet n) → DecSelection (exceptFace missing)
openBoxDecision {n} missing j with discreteEnumeration (facetEnumeration n) j missing
... | yes p = no (λ q → q p)
... | no p = yes p

RawAgreement : {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  → ((j : Facet n) → fst (S j) → Cell A n) → Type ℓ
RawAgreement S A cs = (z : SelectedCodim2 S)
  → reindex A (lowerOverlap (fst z)) (cs (lowerFacet (fst z)) (fst (snd z)))
    ≡ reindex A (upperOverlap (fst z)) (cs (upperFacet (fst z)) (snd (snd z)))

-- 把统一的可枚举关系索引还原为 FaceIntersections 的坐标对接口。
fromRawAgreement : {n : ℕ} (S : FaceSelection n) (A : CubicalSet ℓ)
  (cs : (j : Facet n) → fst (S j) → Cell A n)
  → RawAgreement S A cs → PairwiseFaceData S A
faceCells (fromRawAgreement S A cs eq) = cs
pairwiseAgreement (fromRawAgreement {n = zero} S A cs eq) = lift tt
pairwiseAgreement (fromRawAgreement {n = suc n} S A cs eq) r a b p q = eq ((r , a , b) , p , q)
