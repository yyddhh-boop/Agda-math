{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.LocalizationUniversal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Quasicategories
open import DHH.Simplicial.WalkingIsomorphism
open import DHH.Simplicial.Equivalences
open import DHH.Simplicial.Exponentials
open import DHH.Simplicial.FullSubcomplex
open import DHH.Simplicial.Marked
open import DHH.Simplicial.ExponentialFunctor

private variable ℓX ℓL ℓQ μ : Level

-- 实际后合成保持 E¹ 延拓：把已给定的 WalkingIso→L 与 f 复合。
-- 原有延拓只截断存在；结论也是命题，因此 PT.rec 合法且不选代表。
preserves-E1Invertible : {L : SimplicialSet ℓL} {Q : SimplicialSet ℓQ}
  (f : SimplicialNatural L Q) {e : SCell L 1}
  → E1Invertible L e → E1Invertible Q (mapS f 1 e)
preserves-E1Invertible f {e} = PT.rec squash₁ λ { (h , p) →
  ∣ (h ⋆s f) , simplicialNaturalExt (λ n u →
    cong (mapS f n) (cong (λ k → mapS k n u) p) ∙ naturalS f u e) ∣₁ }

module _ {X : SimplicialSet ℓX} {L : SimplicialSet ℓL}
  (M : Marking X μ) (u : SimplicialNatural X L)
  (marked : PreservesMarking M (equivalencesMarking L) u)
  (Q : SimplicialSet ℓQ) where

  restrictedVertex-marked : (n : ℕ) (h : SCell (ExponentialS L Q) n) (i : Fin (suc n))
    → PreservesMarking M (equivalencesMarking Q)
      (zeroFunctor X (vertexOf (ExponentialS X Q) (mapS (precomposeExponential u Q) n h) i))
  restrictedVertex-marked n h i e w =
    subst (E1Invertible Q)
      (sym (cong (λ k → mapS k 1 e) (vertexFunctor-precompose u Q h i)))
      (preserves-E1Invertible (zeroFunctor L (vertexOf (ExponentialS L Q) h i)) (marked e w))

  -- 预合成的每个顶点都把 W 送到 E¹ 可逆边，故实际落入全子复形。
  -- 不仅给出 restriction 的函数类型，还给出全部单纯自然性证明。
  restriction : SimplicialNatural (ExponentialS L Q) (MarkedFunctorSpace X M Q)
  mapS restriction n h = mapS (precomposeExponential u Q) n h , restrictedVertex-marked n h
  naturalS restriction {m} f h =
    Σ≡Prop (λ c → isPropΠ (λ i → preservesMarking-isProp M (equivalencesMarking Q)
      (zeroFunctor X (vertexOf (ExponentialS X Q) c i))))
      (naturalS (precomposeExponential u Q) f h)

  restriction-cell-projection : (n : ℕ) (h : SCell (ExponentialS L Q) n)
    → fst (mapS restriction n h) ≡ mapS (precomposeExponential u Q) n h
  restriction-cell-projection n h = refl

  restriction-vertex : {n : ℕ} (h : SCell (ExponentialS L Q) n) (i : Fin (suc n))
    → zeroFunctor X (vertexOf (ExponentialS X Q) (fst (mapS restriction n h)) i)
      ≡ u ⋆s zeroFunctor L (vertexOf (ExponentialS L Q) h i)
  restriction-vertex = vertexFunctor-precompose u Q

-- 2306.02218v1 Definition 3.6：限制函子是准范畴等价。
-- κ 明确固定“所有测试目标”的 universe；这不是在有限 Type 层中
-- 偷放 ∀κ。定义一个性质不等于已经为任何候选 L 证明这个性质。
record LocalizationAtTestUniverse (κ : Level)
  (X : SimplicialSet ℓX) (M : Marking X μ)
  (L : SimplicialSet ℓL) (u : SimplicialNatural X L)
  : Type (ℓ-max (ℓ-max ℓX ℓL) (ℓ-max μ (ℓ-suc κ))) where
  field
    localizationSourceQuasicategory : IsQuasicategory X
    localizationTargetQuasicategory : IsQuasicategory L
    unitInvertsMarking : PreservesMarking M (equivalencesMarking L) u
    restrictionEquivalence : (Q : SimplicialSet κ) → IsQuasicategory Q
      → EquivalenceOfQuasicategories (restriction M u unitInvertsMarking Q)
open LocalizationAtTestUniverse public

localizationAtTestUniverse-isProp : (κ : Level)
  (X : SimplicialSet ℓX) (M : Marking X μ) (L : SimplicialSet ℓL) (u : SimplicialNatural X L)
  → isProp (LocalizationAtTestUniverse κ X M L u)
localizationSourceQuasicategory (localizationAtTestUniverse-isProp κ X M L u a b i) =
  isPropIsQuasicategory X (localizationSourceQuasicategory a) (localizationSourceQuasicategory b) i
localizationTargetQuasicategory (localizationAtTestUniverse-isProp κ X M L u a b i) =
  isPropIsQuasicategory L (localizationTargetQuasicategory a) (localizationTargetQuasicategory b) i
unitInvertsMarking (localizationAtTestUniverse-isProp κ X M L u a b i) =
  preservesMarking-isProp M (equivalencesMarking L) u (unitInvertsMarking a) (unitInvertsMarking b) i
restrictionEquivalence (localizationAtTestUniverse-isProp κ X M L u a b i) Q q =
  isProp→PathP
    {B = λ j → EquivalenceOfQuasicategories (restriction M u
      (preservesMarking-isProp M (equivalencesMarking L) u (unitInvertsMarking a) (unitInvertsMarking b) j) Q)}
    (λ j → equivalenceOfQuasicategories-isProp (restriction M u
      (preservesMarking-isProp M (equivalencesMarking L) u (unitInvertsMarking a) (unitInvertsMarking b) j) Q))
    (restrictionEquivalence a Q q) (restrictionEquivalence b Q q) i

-- 边界：本文件没有构造 marked Ex、图的相干 nerve，或证明 DHH。
-- 它使一个具体候选的“局部化泛性质”成为完全展开且可验证的陈述。
