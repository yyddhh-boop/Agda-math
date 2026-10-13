{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Categories.Category.Base using (Category)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Products

private variable ℓ ℓ' ℓ'' : Level

simplexMap : {m n : ℕ} → OrdinalMap m n
  → SimplicialNatural (RepresentableSimplex m) (RepresentableSimplex n)
mapS (simplexMap f) k u = u ⋆o f
naturalS (simplexMap f) u v = Category.⋆Assoc Delta u v f

-- 第n阶记录所有 Δ[n]×A→B 的参数映射。它是无限预层，但每次
-- 操作只接收一个具体单调映射并预合成；没有枚举全体自然变换。
ExponentialS : SimplicialSet ℓ → SimplicialSet ℓ' → SimplicialSet (ℓ-max ℓ ℓ')
simplexes (ExponentialS A B) n =
  SimplicialNatural (SProduct (RepresentableSimplex n) A) B , isSetSimplicialNatural
reindexS (ExponentialS A B) f h = productSMap (simplexMap f) (simplicialId A) ⋆s h
reindexS-id (ExponentialS A B) h = simplicialNaturalExt λ n c →
  cong (λ u → mapS h n (u , snd c)) (Category.⋆IdR Delta (fst c))
reindexS-compose (ExponentialS A B) f g h = simplicialNaturalExt λ n c →
  cong (λ u → mapS h n (u , snd c)) (sym (Category.⋆Assoc Delta (fst c) f g))

evaluationS : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  → SimplicialNatural (SProduct (ExponentialS A B) A) B
mapS evaluationS n (h , a) = mapS h n (ordinalId n , a)
naturalS (evaluationS {A = A} {B = B}) {m} {n} f (h , a) =
  cong (λ u → mapS h m (u , reindexS A f a))
    (Category.⋆IdL Delta f ∙ sym (Category.⋆IdR Delta f))
  ∙ naturalS h f (ordinalId n , a)

curryS : {C : SimplicialSet ℓ} {A : SimplicialSet ℓ'} {B : SimplicialSet ℓ''}
  → SimplicialNatural (SProduct C A) B → SimplicialNatural C (ExponentialS A B)
mapS (mapS (curryS {C = C} h) n c) m (u , a) = mapS h m (reindexS C u c , a)
naturalS (mapS (curryS {C = C} {A = A} h) n c) {l} v (u , a) =
  cong (λ d → mapS h l (d , reindexS A v a)) (reindexS-compose C v u c)
  ∙ naturalS h v (reindexS C u c , a)
naturalS (curryS {C = C} h) f c = simplicialNaturalExt λ m pair →
  cong (λ d → mapS h m (d , snd pair))
    (sym (reindexS-compose C (fst pair) f c))

uncurryS : {C : SimplicialSet ℓ} {A : SimplicialSet ℓ'} {B : SimplicialSet ℓ''}
  → SimplicialNatural C (ExponentialS A B) → SimplicialNatural (SProduct C A) B
uncurryS {C = C} {A = A} {B = B} h =
  productSMap {A = C} {B = ExponentialS A B} {C = A} {D = A} h (simplicialId A)
    ⋆s evaluationS {A = A} {B = B}

uncurry-curryS : {C : SimplicialSet ℓ} {A : SimplicialSet ℓ'} {B : SimplicialSet ℓ''}
  (h : SimplicialNatural (SProduct C A) B)
  → uncurryS {C = C} {A = A} {B = B} (curryS {C = C} {A = A} {B = B} h) ≡ h
uncurry-curryS {C = C} {A = A} {B = B} h =
  simplicialNaturalExt {A = SProduct C A} {B = B} λ n pair →
  cong (λ c → mapS h n (c , snd pair)) (reindexS-id C (fst pair))

curry-uncurryS : {C : SimplicialSet ℓ} {A : SimplicialSet ℓ'} {B : SimplicialSet ℓ''}
  (h : SimplicialNatural C (ExponentialS A B))
  → curryS {C = C} {A = A} {B = B} (uncurryS {C = C} {A = A} {B = B} h) ≡ h
curry-uncurryS {C = C} {A = A} {B = B} h =
  simplicialNaturalExt {A = C} {B = ExponentialS A B} λ n c →
    simplicialNaturalExt {A = SProduct (RepresentableSimplex n) A} {B = B} λ m pair →
  cong (λ k → mapS k m (ordinalId m , snd pair)) (naturalS h (fst pair) c)
  ∙ cong (λ u → mapS (mapS h n c) m (u , snd pair)) (Category.⋆IdL Delta (fst pair))

exponentialSIso : (C : SimplicialSet ℓ) (A : SimplicialSet ℓ') (B : SimplicialSet ℓ'')
  → Iso (SimplicialNatural (SProduct C A) B) (SimplicialNatural C (ExponentialS A B))
Iso.fun (exponentialSIso C A B) = curryS {C = C} {A = A} {B = B}
Iso.inv (exponentialSIso C A B) = uncurryS {C = C} {A = A} {B = B}
Iso.rightInv (exponentialSIso C A B) = curry-uncurryS {C = C} {A = A} {B = B}
Iso.leftInv (exponentialSIso C A B) = uncurry-curryS {C = C} {A = A} {B = B}

exponentialSEquivalence : (C : SimplicialSet ℓ) (A : SimplicialSet ℓ') (B : SimplicialSet ℓ'')
  → SimplicialNatural (SProduct C A) B ≃ SimplicialNatural C (ExponentialS A B)
exponentialSEquivalence C A B = isoToEquiv (exponentialSIso C A B)

-- 这给出实际函子单纯集合所需的参数映射对象和伴随等价；
-- Q为准范畴时Q^A也是准范畴，仍需内角与乘积的提升定理，未预设。
