{-# OPTIONS --cubical --safe #-}

module DHH.Localization.DKEnrichment where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Sigma using (fst; snd)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Cubes using (Position)
open import DHH.Simplicial.Presented
open import DHH.Simplicial.PresentedCategory
open import DHH.Simplicial.PresentedProducts
open import DHH.Localization.RelativeFree
open import DHH.Localization.LevelwiseCore
open import DHH.Localization.LevelwiseFunctor
open import DHH.Localization.DKMapping

private variable ℓ : Level

-- Actual composition in every level of the localized free resolution.
-- As in DKMapping, this uses the all-arrow free-category variant;
-- no equivalence with a classical infinity-localization is assumed.
module _ {C : Category ℓ ℓ} (R : Marking C) where

  composeCell : {x y z : Category.ob C} (n : ℕ)
    → MappingSimplex R x y n → MappingSimplex R y z n
    → MappingSimplex R x z n
  composeCell n = Category._⋆_ (LocalizedResolution R n)

  identityCell : (n : ℕ) (x : Category.ob C) → MappingSimplex R x x n
  identityCell n x = Category.id (LocalizedResolution R n)

  composeCell-face : {n : ℕ} (p : Position (suc (suc n)))
    {x y z : Category.ob C}
    (f : MappingSimplex R x y (suc n)) (g : MappingSimplex R y z (suc n))
    → composeCell n (faceP (DKMapping R x y) p f) (faceP (DKMapping R y z) p g)
      ≡ faceP (DKMapping R x z) p (composeCell (suc n) f g)
  composeCell-face p f g = sym (Functor.F-seq (face R p) f g)

  composeCell-degen : {n : ℕ} (p : Position (suc n))
    {x y z : Category.ob C}
    (f : MappingSimplex R x y n) (g : MappingSimplex R y z n)
    → composeCell (suc n) (degenP (DKMapping R x y) p f) (degenP (DKMapping R y z) p g)
      ≡ degenP (DKMapping R x z) p (composeCell n f g)
  composeCell-degen p f g = sym (Functor.F-seq (degeneracy R p) f g)

  identityCell-face : {n : ℕ} (p : Position (suc (suc n))) (x : Category.ob C)
    → identityCell n x ≡ faceP (DKMapping R x x) p (identityCell (suc n) x)
  identityCell-face p x = sym (Functor.F-id (face R p))

  identityCell-degen : {n : ℕ} (p : Position (suc n)) (x : Category.ob C)
    → identityCell (suc n) x ≡ degenP (DKMapping R x x) p (identityCell n x)
  identityCell-degen p x = sym (Functor.F-id (degeneracy R p))

  composeCell-assoc : {x y z w : Category.ob C} (n : ℕ)
    (f : MappingSimplex R x y n) (g : MappingSimplex R y z n) (h : MappingSimplex R z w n)
    → composeCell n (composeCell n f g) h ≡ composeCell n f (composeCell n g h)
  composeCell-assoc n = Category.⋆Assoc (LocalizedResolution R n)

  composeCell-unit-left : {x y : Category.ob C} (n : ℕ) (f : MappingSimplex R x y n)
    → composeCell n (identityCell n x) f ≡ f
  composeCell-unit-left n = Category.⋆IdL (LocalizedResolution R n)

  composeCell-unit-right : {x y : Category.ob C} (n : ℕ) (f : MappingSimplex R x y n)
    → composeCell n f (identityCell n y) ≡ f
  composeCell-unit-right n = Category.⋆IdR (LocalizedResolution R n)

module _ {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
         (F : RelativeFunctor R S) where

  mappingMap-composeCell : {x y z : Category.ob C} (n : ℕ)
    (f : MappingSimplex R x y n) (g : MappingSimplex R y z n)
    → mapPCell (DKMappingMap F x z) n (composeCell R n f g)
      ≡ composeCell S n (mapPCell (DKMappingMap F x y) n f)
                         (mapPCell (DKMappingMap F y z) n g)
  mappingMap-composeCell n = Functor.F-seq (LevelFunctor F n)

  mappingMap-identityCell : (n : ℕ) (x : Category.ob C)
    → mapPCell (DKMappingMap F x x) n (identityCell R n x)
      ≡ identityCell S n (Functor.F-ob (RelativeFunctor.functor F) x)
  mappingMap-identityCell n x = Functor.F-id (LevelFunctor F n)

-- Composition and identities are maps of the actual presented
-- simplicial sets, not just arbitrary operations on their cells.
module _ {C : Category ℓ ℓ} (R : Marking C) where

  DKcomposition : (x y z : Category.ob C)
    → PresentedNatural (presentedProduct (DKMapping R x y) (DKMapping R y z))
                       (DKMapping R x z)
  mapPCell (DKcomposition x y z) n (f , g) = composeCell R n f g
  face-naturalP (DKcomposition x y z) p (f , g) = composeCell-face R p f g
  degen-naturalP (DKcomposition x y z) p (f , g) = composeCell-degen R p f g

  DKidentity : (x : Category.ob C)
    → PresentedNatural (presentedTerminal ℓ) (DKMapping R x x)
  mapPCell (DKidentity x) n _ = identityCell R n x
  face-naturalP (DKidentity x) p _ = identityCell-face R p x
  degen-naturalP (DKidentity x) p _ = identityCell-degen R p x

  DKleftUnit : (x y : Category.ob C)
    → PresentedNatural (DKMapping R x y) (DKMapping R x y)
  DKleftUnit x y = presentedCompose
    (presentedPairing
      (presentedCompose (terminalMap (DKMapping R x y)) (DKidentity x))
      (presentedIdentity (DKMapping R x y)))
    (DKcomposition x x y)

  DKrightUnit : (x y : Category.ob C)
    → PresentedNatural (DKMapping R x y) (DKMapping R x y)
  DKrightUnit x y = presentedCompose
    (presentedPairing
      (presentedIdentity (DKMapping R x y))
      (presentedCompose (terminalMap (DKMapping R x y)) (DKidentity y)))
    (DKcomposition x y y)

  DKleftUnit-law : (x y : Category.ob C)
    → DKleftUnit x y ≡ presentedIdentity (DKMapping R x y)
  DKleftUnit-law x y = presentedNaturalExt (λ n f → composeCell-unit-left R n f)

  DKrightUnit-law : (x y : Category.ob C)
    → DKrightUnit x y ≡ presentedIdentity (DKMapping R x y)
  DKrightUnit-law x y = presentedNaturalExt (λ n f → composeCell-unit-right R n f)

  -- Both sides have the SAME product domain.  The projections and
  -- pairings implement the associativity diagram without introducing
  -- an implicit equality between differently parenthesized products.
  DKtriple : (x y z w : Category.ob C) → PresentedSimplicialSet ℓ
  DKtriple x y z w = presentedProduct (DKMapping R x y)
    (presentedProduct (DKMapping R y z) (DKMapping R z w))

  DKassocLeft : (x y z w : Category.ob C)
    → PresentedNatural (DKtriple x y z w) (DKMapping R x w)
  DKassocLeft x y z w = presentedCompose
    (presentedPairing
      (presentedCompose
        (presentedPairing
          (firstProjection {A = DKMapping R x y}
            {B = presentedProduct (DKMapping R y z) (DKMapping R z w)})
          (presentedCompose
            (secondProjection {A = DKMapping R x y}
              {B = presentedProduct (DKMapping R y z) (DKMapping R z w)})
            (firstProjection {A = DKMapping R y z} {B = DKMapping R z w})))
        (DKcomposition x y z))
      (presentedCompose
        (secondProjection {A = DKMapping R x y}
          {B = presentedProduct (DKMapping R y z) (DKMapping R z w)})
        (secondProjection {A = DKMapping R y z} {B = DKMapping R z w})))
    (DKcomposition x z w)

  DKassocRight : (x y z w : Category.ob C)
    → PresentedNatural (DKtriple x y z w) (DKMapping R x w)
  DKassocRight x y z w = presentedCompose
    (productMap (presentedIdentity (DKMapping R x y)) (DKcomposition y z w))
    (DKcomposition x y w)

  DKassociative-law : (x y z w : Category.ob C)
    → DKassocLeft x y z w ≡ DKassocRight x y z w
  DKassociative-law x y z w = presentedNaturalExt
    (λ n fg → composeCell-assoc R n (fst fg) (fst (snd fg)) (snd (snd fg)))

-- A relative functor gives an enrichment-preserving map.  These are
-- equalities of natural transformations, hence apply to every simplex
-- and commute with all ordinal operators through presentedPresheaf.
module _ {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
         (F : RelativeFunctor R S) where

  mappingMap-preserves-composition : (x y z : Category.ob C)
    → presentedCompose (DKcomposition R x y z) (DKMappingMap F x z)
      ≡ presentedCompose
          (productMap (DKMappingMap F x y) (DKMappingMap F y z))
          (DKcomposition S (Functor.F-ob (RelativeFunctor.functor F) x)
                           (Functor.F-ob (RelativeFunctor.functor F) y)
                           (Functor.F-ob (RelativeFunctor.functor F) z))
  mappingMap-preserves-composition x y z = presentedNaturalExt
    (λ n fg → mappingMap-composeCell F n (fst fg) (snd fg))

  mappingMap-preserves-identity : (x : Category.ob C)
    → presentedCompose (DKidentity R x) (DKMappingMap F x x)
      ≡ DKidentity S (Functor.F-ob (RelativeFunctor.functor F) x)
  mappingMap-preserves-identity x = presentedNaturalExt
    (λ n _ → mappingMap-identityCell F n x)

-- This packages the concrete construction as a simplicial enriched
-- category.  Its object type need not be a set: comparing this internal
-- formulation with the classical object-set DK model remains separate.
record PresentedEnrichedCategory (ℓo ℓh : Level) : Type (ℓ-suc (ℓ-max ℓo ℓh)) where
  field
    objects : Type ℓo
    mapping : objects → objects → PresentedSimplicialSet ℓh
    enrichedIdentity : (x : objects)
      → PresentedNatural (presentedTerminal ℓh) (mapping x x)
    enrichedComposition : (x y z : objects)
      → PresentedNatural (presentedProduct (mapping x y) (mapping y z)) (mapping x z)
    enrichedUnitL : {x y : objects} (n : ℕ) (f : PCell (mapping x y) n)
      → mapPCell (enrichedComposition x x y) n
          (mapPCell (enrichedIdentity x) n tt* , f) ≡ f
    enrichedUnitR : {x y : objects} (n : ℕ) (f : PCell (mapping x y) n)
      → mapPCell (enrichedComposition x y y) n
          (f , mapPCell (enrichedIdentity y) n tt*) ≡ f
    enrichedAssoc : {x y z w : objects} (n : ℕ)
      (f : PCell (mapping x y) n) (g : PCell (mapping y z) n) (h : PCell (mapping z w) n)
      → mapPCell (enrichedComposition x z w) n
          (mapPCell (enrichedComposition x y z) n (f , g) , h)
        ≡ mapPCell (enrichedComposition x y w) n
          (f , mapPCell (enrichedComposition y z w) n (g , h))
open PresentedEnrichedCategory public

DKEnrichedCategory : {C : Category ℓ ℓ} (R : Marking C) → PresentedEnrichedCategory ℓ ℓ
objects (DKEnrichedCategory {C = C} R) = Category.ob C
mapping (DKEnrichedCategory {C = C} R) x y = DKMapping {C = C} R x y
enrichedIdentity (DKEnrichedCategory {C = C} R) x = DKidentity {C = C} R x
enrichedComposition (DKEnrichedCategory {C = C} R) x y z = DKcomposition {C = C} R x y z
enrichedUnitL (DKEnrichedCategory {C = C} R) {x = x} {y = y} n f =
  composeCell-unit-left {C = C} R {x = x} {y = y} n f
enrichedUnitR (DKEnrichedCategory {C = C} R) {x = x} {y = y} n f =
  composeCell-unit-right {C = C} R {x = x} {y = y} n f
enrichedAssoc (DKEnrichedCategory {C = C} R) {x = x} {y = y} {z = z} {w = w} n f g h =
  composeCell-assoc {C = C} R {x = x} {y = y} {z = z} {w = w} n f g h

record PresentedEnrichedFunctor {ℓo ℓo' ℓh : Level}
  (A : PresentedEnrichedCategory ℓo ℓh) (B : PresentedEnrichedCategory ℓo' ℓh)
  : Type (ℓ-max ℓo (ℓ-max ℓo' ℓh)) where
  field
    objectMap : objects A → objects B
    mappingMap : (x y : objects A)
      → PresentedNatural (mapping A x y) (mapping B (objectMap x) (objectMap y))
    enrichedIdentityPreserved : (n : ℕ) (x : objects A)
      → mapPCell (mappingMap x x) n (mapPCell (enrichedIdentity A x) n tt*)
        ≡ mapPCell (enrichedIdentity B (objectMap x)) n tt*
    enrichedCompositionPreserved : {x y z : objects A} (n : ℕ)
      (f : PCell (mapping A x y) n) (g : PCell (mapping A y z) n)
      → mapPCell (mappingMap x z) n (mapPCell (enrichedComposition A x y z) n (f , g))
        ≡ mapPCell (enrichedComposition B (objectMap x) (objectMap y) (objectMap z)) n
            (mapPCell (mappingMap x y) n f , mapPCell (mappingMap y z) n g)
open PresentedEnrichedFunctor public

DKEnrichedFunctor : {C D : Category ℓ ℓ} {R : Marking C} {S : Marking D}
  (F : RelativeFunctor R S) → PresentedEnrichedFunctor (DKEnrichedCategory R) (DKEnrichedCategory S)
objectMap (DKEnrichedFunctor {C = C} {D = D} {R = R} {S = S} F) =
  Functor.F-ob (RelativeFunctor.functor F)
mappingMap (DKEnrichedFunctor {C = C} {D = D} {R = R} {S = S} F) x y =
  DKMappingMap {C = C} {D = D} {R = R} {S = S} F x y
enrichedIdentityPreserved (DKEnrichedFunctor {C = C} {D = D} {R = R} {S = S} F) n x =
  mappingMap-identityCell {C = C} {D = D} {R = R} {S = S} F n x
enrichedCompositionPreserved (DKEnrichedFunctor {C = C} {D = D} {R = R} {S = S} F)
  {x = x} {y = y} {z = z} n f g =
  mappingMap-composeCell {C = C} {D = D} {R = R} {S = S} F
    {x = x} {y = y} {z = z} n f g
