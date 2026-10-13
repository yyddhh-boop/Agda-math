{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.NormalizedComposition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Categories.Category.Base using (Category)
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation
open import DHH.Simplicial.NormalForm
open import DHH.Simplicial.WordNormalization
open import DHH.Simplicial.PresentationCompleteness
open import DHH.Simplicial.DecidableWords using (normalize-compose; normalize-normalWord)

-- 复用两个已经计算的范式：把第二个范式递归读成生成词，
-- 再增量加入第一个范式。没有枚举所有中间单调映射。
-- 这里证明算法的复合律，不声称此实现已经达到最优复杂度。
infixl 20 _⋆N_
_⋆N_ : {m n k : ℕ} → Normal m n → Normal n k → Normal m k
p ⋆N q = appendWord p (normalWord q)

appendWord-semantics : {m n k : ℕ} (p : Normal m n) (w : DeltaWord n k)
  → normalSemantics (appendWord p w) ≡ normalSemantics p ⋆o evalWord w
appendWord-semantics p w =
  sym (normal-word-evaluation (appendWord p w))
  ∙ sym (cong evaluatePresented (appendWord-sound p w))
  ∙ cong (_⋆o evalWord w) (normal-word-evaluation p)

normalized-compose-semantics : {m n k : ℕ} (p : Normal m n) (q : Normal n k)
  → normalSemantics (p ⋆N q) ≡ normalSemantics p ⋆o normalSemantics q
normalized-compose-semantics p q = appendWord-semantics p (normalWord q)
  ∙ cong (normalSemantics p ⋆o_) (normal-word-evaluation q)

identityNormal-semantics : (n : ℕ) → normalSemantics (identityNormal n) ≡ ordinalId n
identityNormal-semantics n = sym (normal-word-evaluation (identityNormal n))
  ∙ cong evaluatePresented (identityNormal-sound n)

-- 三条范畴律由已证语义可靠性与范式语义单射导出。
-- 单射本身是 NormalForm 中的结构归纳，不是额外相等公理。
normalized-left-unit : {m n : ℕ} (p : Normal m n) → identityNormal m ⋆N p ≡ p
normalized-left-unit {m} p = normal-semantic-injective _ p
  (normalized-compose-semantics (identityNormal m) p
  ∙ cong (_⋆o normalSemantics p) (identityNormal-semantics m)
  ∙ Category.⋆IdL Delta (normalSemantics p))

normalized-right-unit : {m n : ℕ} (p : Normal m n) → p ⋆N identityNormal n ≡ p
normalized-right-unit {n = n} p = normal-semantic-injective _ p
  (normalized-compose-semantics p (identityNormal n)
  ∙ cong (normalSemantics p ⋆o_) (identityNormal-semantics n)
  ∙ Category.⋆IdR Delta (normalSemantics p))

normalized-associativity : {l m n k : ℕ}
  (p : Normal l m) (q : Normal m n) (r : Normal n k)
  → (p ⋆N q) ⋆N r ≡ p ⋆N (q ⋆N r)
normalized-associativity p q r = normal-semantic-injective _ _
  (normalized-compose-semantics (p ⋆N q) r
  ∙ cong (_⋆o normalSemantics r) (normalized-compose-semantics p q)
  ∙ Category.⋆Assoc Delta (normalSemantics p) (normalSemantics q) (normalSemantics r)
  ∙ cong (normalSemantics p ⋆o_) (sym (normalized-compose-semantics q r))
  ∙ sym (normalized-compose-semantics p (q ⋆N r)))

-- 先规范化两段再复合，与先复合原词再规范化，得到同一范式。
-- 因而后续组合可以保留范式缓存，而不必保存或重新处理原词。
normalization-preserves-composition : {m n k : ℕ}
  (f : DeltaWord m n) (g : DeltaWord n k)
  → normalizeWord (seqW f g) ≡ normalizeWord f ⋆N normalizeWord g
normalization-preserves-composition f g = normal-semantic-injective _ _
  (normalization-evaluation (seqW f g)
  ∙ cong₂ _⋆o_ (sym (normalization-evaluation f)) (sym (normalization-evaluation g))
  ∙ sym (normalized-compose-semantics (normalizeWord f) (normalizeWord g)))
