{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.FullSubcomplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Categories.Category.Base using (Category)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Sets

private variable ℓ ℓp : Level

constantOrdinal : (m n : ℕ) → Fin (suc n) → OrdinalMap m n
mapIndex (constantOrdinal m n i) j = i
monotone (constantOrdinal m n i) j k p = ≤F-refl i

vertexOrdinal : {n : ℕ} → Fin (suc n) → OrdinalMap 0 n
vertexOrdinal {n} = constantOrdinal 0 n

vertexOf : (A : SimplicialSet ℓ) {n : ℕ} → SCell A n → Fin (suc n) → SCell A 0
vertexOf A c i = reindexS A (vertexOrdinal i) c

vertex-reindex : (A : SimplicialSet ℓ) {m n : ℕ} (f : OrdinalMap m n)
  (c : SCell A n) (i : Fin (suc m))
  → vertexOf A (reindexS A f c) i ≡ vertexOf A c (mapIndex f i)
vertex-reindex A f c i =
  sym (reindexS-compose A (vertexOrdinal i) f c)
  ∙ cong (λ u → reindexS A u c) (ordinalMapExt (λ _ → refl))

-- 全子复形只限制顶点；高维 cell 和所有重索引来自原单纯集合。
-- 为有限个顶点逐项保存性质的证据；P另有判定程序时才得到检查算法。
FullSubcomplex : (A : SimplicialSet ℓ) → (SCell A 0 → hProp ℓp)
  → SimplicialSet (ℓ-max ℓ ℓp)
simplexes (FullSubcomplex A P) n =
  (Σ[ c ∈ SCell A n ] ((i : Fin (suc n)) → fst (P (vertexOf A c i)))) ,
  isSetΣSndProp (snd (simplexes A n)) (λ c → isPropΠ (λ i → snd (P (vertexOf A c i))))
reindexS (FullSubcomplex A P) f (c , p) =
  reindexS A f c , λ i → subst (λ v → fst (P v))
    (sym (vertex-reindex A f c i)) (p (mapIndex f i))
reindexS-id (FullSubcomplex A P) (c , p) =
  Σ≡Prop (λ c → isPropΠ (λ i → snd (P (vertexOf A c i)))) (reindexS-id A c)
reindexS-compose (FullSubcomplex A P) f g (c , p) =
  Σ≡Prop (λ c → isPropΠ (λ i → snd (P (vertexOf A c i)))) (reindexS-compose A f g c)

fullInclusion : (A : SimplicialSet ℓ) (P : SCell A 0 → hProp ℓp)
  → SimplicialNatural (FullSubcomplex A P) A
mapS (fullInclusion A P) n = fst
naturalS (fullInclusion A P) f c = refl

fullInclusion-injective : (A : SimplicialSet ℓ) (P : SCell A 0 → hProp ℓp)
  (n : ℕ) (c d : SCell (FullSubcomplex A P) n)
  → fst c ≡ fst d → c ≡ d
fullInclusion-injective A P n c d =
  Σ≡Prop (λ c → isPropΠ (λ i → snd (P (vertexOf A c i))))
