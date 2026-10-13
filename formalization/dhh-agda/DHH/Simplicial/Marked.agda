{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Marked where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Products
open import DHH.Simplicial.Exponentials
open import DHH.Simplicial.WalkingIsomorphism
open import DHH.Simplicial.FullSubcomplex

private variable ℓ ℓ' μ ν : Level

-- 标记是1-simplex的命题性质，并要求所有退化边被标记。
-- 原文 W 必须在此槽位给出实际图弱等价；不能由调用者任意改名。
record Marking (A : SimplicialSet ℓ) (μ : Level) : Type (ℓ-max ℓ (ℓ-suc μ)) where
  field
    markedEdge : SCell A 1 → hProp μ
    markedDegenerate : (x : SCell A 0)
      → fst (markedEdge (reindexS A (codegeneracy fzero) x))
open Marking public

PreservesMarking : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  → Marking A μ → Marking B ν → SimplicialNatural A B
  → Type (ℓ-max ℓ (ℓ-max μ ν))
PreservesMarking M N f = (e : _) → fst (markedEdge M e)
  → fst (markedEdge N (mapS f 1 e))

preservesMarking-isProp : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  (M : Marking A μ) (N : Marking B ν) (f : SimplicialNatural A B)
  → isProp (PreservesMarking M N f)
preservesMarking-isProp M N f = isPropΠ2 λ e p → snd (markedEdge N (mapS f 1 e))

booleanVertex : Fin 2 → Bool
booleanVertex fzero = false
booleanVertex (fsuc fzero) = true
booleanVertex (fsuc (fsuc ()))

isoEdge : SimplicialNatural (RepresentableSimplex 1) WalkingIso
mapS isoEdge n u i = booleanVertex (mapIndex u i)
naturalS isoEdge f u = refl

-- Definition 2.3：边Δ¹→Q沿Δ¹→E¹延拓。这个定义可直接检查
-- 原文的“把W变为等价”条件，不借用拓扑空间的弱等价。
E1Invertible : (Q : SimplicialSet ℓ) → SCell Q 1 → Type ℓ
E1Invertible Q e = ∥ Σ[ h ∈ SimplicialNatural WalkingIso Q ]
  (isoEdge ⋆s h ≡ classifySimplex Q e) ∥₁

zeroIndex-unique : (i : Fin 1) → i ≡ fzero
zeroIndex-unique fzero = refl
zeroIndex-unique (fsuc ())

ordinalToZero-unique : {n : ℕ} (f : OrdinalMap n 0)
  → f ≡ constantOrdinal n 0 fzero
ordinalToZero-unique f = ordinalMapExt λ i → zeroIndex-unique (mapIndex f i)

constantS : {A : SimplicialSet ℓ'} (Q : SimplicialSet ℓ) (q : SCell Q 0)
  → SimplicialNatural A Q
mapS (constantS Q q) n c = reindexS Q (constantOrdinal n 0 fzero) q
naturalS (constantS Q q) {m} {n} f c =
  cong (λ u → reindexS Q u q) (sym (ordinalToZero-unique (f ⋆o constantOrdinal n 0 fzero)))
  ∙ reindexS-compose Q f (constantOrdinal n 0 fzero) q

equivalencesMarking : (Q : SimplicialSet ℓ) → Marking Q ℓ
markedEdge (equivalencesMarking Q) e = E1Invertible Q e , squash₁
markedDegenerate (equivalencesMarking Q) q =
  ∣ (constantS {A = WalkingIso} Q q , simplicialNaturalExt (λ n u →
    cong (λ v → reindexS Q v q)
      (sym (ordinalToZero-unique (u ⋆o codegeneracy fzero)))
    ∙ reindexS-compose Q u (codegeneracy fzero) q)) ∣₁

zeroParameter : (A : SimplicialSet ℓ)
  → SimplicialNatural A (SProduct (RepresentableSimplex 0) A)
zeroParameter A = pairS (constantS (RepresentableSimplex 0) (ordinalId 0)) (simplicialId A)

zeroFunctor : (A : SimplicialSet ℓ) {Q : SimplicialSet ℓ'}
  → SCell (ExponentialS A Q) 0 → SimplicialNatural A Q
zeroFunctor A h = zeroParameter A ⋆s h

-- 原论文 Definition 3.6 使用的函子准范畴 Fun_W(A,Q)：
-- 从实际指数对象中，取“将所有标记边送为可逆边”的全子复形。
-- 全子复形的准范畴性仍需证明；本模块没有将此性质作为定义附赠。
MarkedFunctorSpace : (A : SimplicialSet ℓ) → Marking A μ
  → SimplicialSet ℓ' → SimplicialSet (ℓ-max ℓ (ℓ-max ℓ' μ))
MarkedFunctorSpace A M Q = FullSubcomplex (ExponentialS A Q)
  (λ h → PreservesMarking M (equivalencesMarking Q) (zeroFunctor A h) ,
    preservesMarking-isProp M (equivalencesMarking Q) (zeroFunctor A h))
