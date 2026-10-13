{-# OPTIONS --cubical --safe #-}

module DHH.Localization.ResolutionOperators where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Cubes using (Position; here; there; weakenPosition;
  CoordinatePair; front; under; lower; upper; lowerWide; upperWide)
open import DHH.Localization.FreeCategory

private
  variable ℓ : Level

-- Work in one universe for objects and arrows, so iteration does not
-- change a category's declared hom level.  LiftHoms from the library
-- puts a category such as GraphCategory into this form.
-- 构造视角：Power C n 迭代 n 次自由范畴构造，对自然数结构递归。
-- collapse/duplicate 再对 Position 递归，决定在哪一层求值或加层。
-- 单纯恒等式由 epsilon/delta 的自然性及 comonad 律统一推出；
-- 这给全部有限阶段的结构，不自动给无限极限、Kan 填充或经典 DK 比较。
Power : Category ℓ ℓ → ℕ → Category ℓ ℓ
Category.ob (Power C n) = Category.ob C
Category.Hom[_,_] (Power C zero) = Category.Hom[_,_] C
Category.Hom[_,_] (Power C (suc n)) = Category.Hom[_,_] (Free (Power C n))
Category.id (Power C zero) = Category.id C
Category.id (Power C (suc n)) = Category.id (Free (Power C n))
Category._⋆_ (Power C zero) = Category._⋆_ C
Category._⋆_ (Power C (suc n)) = Category._⋆_ (Free (Power C n))
Category.⋆IdL (Power C zero) = Category.⋆IdL C
Category.⋆IdL (Power C (suc n)) = Category.⋆IdL (Free (Power C n))
Category.⋆IdR (Power C zero) = Category.⋆IdR C
Category.⋆IdR (Power C (suc n)) = Category.⋆IdR (Free (Power C n))
Category.⋆Assoc (Power C zero) = Category.⋆Assoc C
Category.⋆Assoc (Power C (suc n)) = Category.⋆Assoc (Free (Power C n))
Category.isSetHom (Power C zero) = Category.isSetHom C
Category.isSetHom (Power C (suc n)) = Category.isSetHom (Free (Power C n))

Resolution : Category ℓ ℓ → ℕ → Category ℓ ℓ
Resolution C n = Power C (suc n)

module _ (C : Category ℓ ℓ) where

  collapse : {n : ℕ} → Position (suc n)
           → Functor (Power C (suc n)) (Power C n)
  Functor.F-ob (collapse i) x = x
  Functor.F-hom (collapse {n = n} here) = Functor.F-hom (epsilon (Power C n))
  Functor.F-hom (collapse {n = suc n} (there i)) = Functor.F-hom (FreeFunctor (collapse i))
  Functor.F-id (collapse {n = n} here) = Functor.F-id (epsilon (Power C n))
  Functor.F-id (collapse {n = suc n} (there i)) = Functor.F-id (FreeFunctor (collapse i))
  Functor.F-seq (collapse {n = n} here) = Functor.F-seq (epsilon (Power C n))
  Functor.F-seq (collapse {n = suc n} (there i)) = Functor.F-seq (FreeFunctor (collapse i))

  duplicate : {n : ℕ} → Position (suc n)
            → Functor (Power C (suc n)) (Power C (suc (suc n)))
  Functor.F-ob (duplicate i) x = x
  Functor.F-hom (duplicate {n = n} here) = Functor.F-hom (delta (Power C n))
  Functor.F-hom (duplicate {n = suc n} (there i)) = Functor.F-hom (FreeFunctor (duplicate i))
  Functor.F-id (duplicate {n = n} here) = Functor.F-id (delta (Power C n))
  Functor.F-id (duplicate {n = suc n} (there i)) = Functor.F-id (FreeFunctor (duplicate i))
  Functor.F-seq (duplicate {n = n} here) = Functor.F-seq (delta (Power C n))
  Functor.F-seq (duplicate {n = suc n} (there i)) = Functor.F-seq (FreeFunctor (duplicate i))

  face : {n : ℕ} → Position (suc (suc n))
       → Functor (Resolution C (suc n)) (Resolution C n)
  face = collapse

  degeneracy : {n : ℕ} → Position (suc n)
             → Functor (Resolution C n) (Resolution C (suc n))
  degeneracy = duplicate

  -- Hom-level proofs are kept separate.  Every assembled functor path
  -- has a definitionally constant object component, even when its
  -- coordinate index is a variable.
  mutual
    faces-commute : {n : ℕ} (p : CoordinatePair n)
      → funcComp (collapse (upper p)) (collapse (lowerWide p))
        ≡ funcComp (collapse (lower p)) (collapse (upperWide p))
    faces-commute p = Functor≡ (λ _ → refl) (facesHom p)

    facesHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
      (f : Category.Hom[_,_] (Power C (suc (suc n))) x y)
      → Functor.F-hom (funcComp (collapse (upper p)) (collapse (lowerWide p))) f
        ≡ Functor.F-hom (funcComp (collapse (lower p)) (collapse (upperWide p))) f
    facesHom (front j) f i = Functor.F-hom (epsilon-natural (collapse j) (~ i)) f
    facesHom (under p) f =
      (λ i → Functor.F-hom (FreeFunctor-composition
        (collapse (lowerWide p)) (collapse (upper p)) (~ i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor (faces-commute p i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor-composition
        (collapse (upperWide p)) (collapse (lower p)) i) f)

  mutual
    degeneracies-commute : {n : ℕ} (p : CoordinatePair n)
      → funcComp (duplicate (lowerWide p)) (duplicate (upper p))
        ≡ funcComp (duplicate (upperWide p)) (duplicate (lower p))
    degeneracies-commute p = Functor≡ (λ _ → refl) (degensHom p)

    degensHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
      (f : Category.Hom[_,_] (Power C (suc n)) x y)
      → Functor.F-hom (funcComp (duplicate (lowerWide p)) (duplicate (upper p))) f
        ≡ Functor.F-hom (funcComp (duplicate (upperWide p)) (duplicate (lower p))) f
    degensHom {n = n} (front here) f i = Functor.F-hom (delta-coassoc (Power C n) i) f
    degensHom {n = suc n} (front (there j)) f i = Functor.F-hom (delta-natural (duplicate j) i) f
    degensHom (under p) f =
      (λ i → Functor.F-hom (FreeFunctor-composition
        (duplicate (upper p)) (duplicate (lowerWide p)) (~ i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor (degeneracies-commute p i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor-composition
        (duplicate (lower p)) (duplicate (upperWide p)) i) f)

  mutual
    face-degeneracy-same : {n : ℕ} (i : Position (suc n))
      → funcComp (collapse (weakenPosition i)) (duplicate i) ≡ Id
    face-degeneracy-same i = Functor≡ (λ _ → refl) (sameHom i)

    sameHom : {n : ℕ} (i : Position (suc n)) {x y : Category.ob C}
      (f : Category.Hom[_,_] (Power C (suc n)) x y)
      → Functor.F-hom (funcComp (collapse (weakenPosition i)) (duplicate i)) f ≡ f
    sameHom {n = n} here f j = Functor.F-hom (epsilon-delta (Power C n) j) f
    sameHom {n = suc n} (there i) f =
      (λ j → Functor.F-hom (FreeFunctor-composition (duplicate i)
        (collapse (weakenPosition i)) (~ j)) f)
      ∙ (λ j → Functor.F-hom (FreeFunctor (face-degeneracy-same i j)) f)
      ∙ (λ j → Functor.F-hom (FreeFunctor-identity (Power C (suc n)) j) f)

  mutual
    face-degeneracy-next : {n : ℕ} (i : Position (suc n))
      → funcComp (collapse (there i)) (duplicate i) ≡ Id
    face-degeneracy-next i = Functor≡ (λ _ → refl) (nextHom i)

    nextHom : {n : ℕ} (i : Position (suc n)) {x y : Category.ob C}
      (f : Category.Hom[_,_] (Power C (suc n)) x y)
      → Functor.F-hom (funcComp (collapse (there i)) (duplicate i)) f ≡ f
    nextHom {n = n} here f j = Functor.F-hom (Free-epsilon-delta (Power C n) j) f
    nextHom {n = suc n} (there i) f =
      (λ j → Functor.F-hom (FreeFunctor-composition (duplicate i)
        (collapse (there i)) (~ j)) f)
      ∙ (λ j → Functor.F-hom (FreeFunctor (face-degeneracy-next i j)) f)
      ∙ (λ j → Functor.F-hom (FreeFunctor-identity (Power C (suc n)) j) f)

  mutual
    face-degeneracy-before : {n : ℕ} (p : CoordinatePair n)
      → funcComp (collapse (weakenPosition (lowerWide p))) (duplicate (upperWide p))
        ≡ funcComp (duplicate (upper p)) (collapse (lowerWide p))
    face-degeneracy-before p = Functor≡ (λ _ → refl) (beforeHom p)

    beforeHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
      (f : Category.Hom[_,_] (Power C (suc (suc n))) x y)
      → Functor.F-hom (funcComp (collapse (weakenPosition (lowerWide p))) (duplicate (upperWide p))) f
        ≡ Functor.F-hom (funcComp (duplicate (upper p)) (collapse (lowerWide p))) f
    beforeHom (front j) f i = Functor.F-hom (epsilon-natural (duplicate j) i) f
    beforeHom (under p) f =
      (λ i → Functor.F-hom (FreeFunctor-composition (duplicate (upperWide p))
        (collapse (weakenPosition (lowerWide p))) (~ i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor (face-degeneracy-before p i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor-composition
        (collapse (lowerWide p)) (duplicate (upper p)) i) f)

  mutual
    face-degeneracy-after : {n : ℕ} (p : CoordinatePair n)
      → funcComp (collapse (there (upperWide p))) (duplicate (lowerWide p))
        ≡ funcComp (duplicate (lower p)) (collapse (upperWide p))
    face-degeneracy-after p = Functor≡ (λ _ → refl) (afterHom p)

    afterHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
      (f : Category.Hom[_,_] (Power C (suc (suc n))) x y)
      → Functor.F-hom (funcComp (collapse (there (upperWide p))) (duplicate (lowerWide p))) f
        ≡ Functor.F-hom (funcComp (duplicate (lower p)) (collapse (upperWide p))) f
    afterHom (front j) f i = Functor.F-hom (delta-natural (collapse j) (~ i)) f
    afterHom (under p) f =
      (λ i → Functor.F-hom (FreeFunctor-composition
        (duplicate (lowerWide p)) (collapse (there (upperWide p))) (~ i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor (face-degeneracy-after p i)) f)
      ∙ (λ i → Functor.F-hom (FreeFunctor-composition
        (collapse (upperWide p)) (duplicate (lower p)) i) f)
