{-# OPTIONS --cubical --safe #-}

module DHH.Simplicial.DecidableWords where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (znots; injSucFin)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Relation.Nullary using (Dec; yes; no)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation
open import DHH.Simplicial.NormalForm
open import DHH.Simplicial.WordNormalization
open import DHH.Simplicial.PresentationCompleteness

-- 输入是同源、同目标的两个有限 Δ 生成词，不要求枚举单调映射。
-- 先实际计算各自的范式，再沿两个范式的构造树递归比较。
-- nzero 不降低维数；终止依据是互递归语法树的真子项，
-- 而不是“每一步源维数或目标维数都严格下降”。
-- 不同构造的排除证书只检查首值或第二值；同构造则递归其子项。
mutual
  normalEquality? : {m n : ℕ} (p q : Normal m n) → Dec (p ≡ q)
  normalEquality? (nzero z) (nzero w) with zeroNormalEquality? z w
  ... | yes e = yes (cong nzero e)
  ... | no ne = no (λ e → ne (zero-semantic-injective z w (cong normalSemantics e)))
  normalEquality? (nzero z) (nshift q) = no λ e →
    znots (sym (zero-head z) ∙ cong (λ r → mapIndex (normalSemantics r) fzero) e)
  normalEquality? (nshift p) (nzero w) = no λ e →
    znots (sym (zero-head w) ∙ cong (λ r → mapIndex (normalSemantics r) fzero) (sym e))
  normalEquality? (nshift p) (nshift q) with normalEquality? p q
  ... | yes e = yes (cong nshift e)
  ... | no ne = no (λ e → ne (normal-semantic-injective p q (ordinalMapExt λ x →
    injSucFin (cong (λ r → mapIndex (normalSemantics r) x) e))))

  zeroNormalEquality? : {m n : ℕ} (p q : ZeroNormal m n) → Dec (p ≡ q)
  zeroNormalEquality? zvertex zvertex = yes refl
  zeroNormalEquality? (zrepeat z) (zrepeat w) with zeroNormalEquality? z w
  ... | yes e = yes (cong zrepeat e)
  ... | no ne = no (λ e → ne (zero-semantic-injective z w (ordinalMapExt λ x →
    cong (λ r → mapIndex (zeroSemantics r) (fsuc x)) e)))
  zeroNormalEquality? (zrepeat z) (zlift q) = no λ e →
    znots (sym (zero-head z) ∙ cong (λ r → mapIndex (zeroSemantics r) (fsuc fzero)) e)
  zeroNormalEquality? (zlift p) (zrepeat w) = no λ e →
    znots (sym (zero-head w) ∙ cong (λ r → mapIndex (zeroSemantics r) (fsuc fzero)) (sym e))
  zeroNormalEquality? (zlift p) (zlift q) with normalEquality? p q
  ... | yes e = yes (cong zlift e)
  ... | no ne = no (λ e → ne (normal-semantic-injective p q (ordinalMapExt λ x →
    injSucFin (cong (λ r → mapIndex (zeroSemantics r) (fsuc x)) e))))

-- 两个方向都经过已证明的规范化与原始关系商：这里没有给
-- WordRelation 新增“语义相等”或“范式相等”作为公理。
normal-equality→word-equality : {m n : ℕ} (f g : DeltaWord m n)
  → normalizeWord f ≡ normalizeWord g → SQ.[ f ] ≡ SQ.[ g ]
normal-equality→word-equality f g p = word-evaluation-faithful f g
  (sym (normalization-evaluation f) ∙ cong normalSemantics p ∙ normalization-evaluation g)

word-equality→normal-equality : {m n : ℕ} (f g : DeltaWord m n)
  → SQ.[ f ] ≡ SQ.[ g ] → normalizeWord f ≡ normalizeWord g
word-equality→normal-equality f g p =
  normal-semantic-injective (normalizeWord f) (normalizeWord g)
    (normalization-evaluation f ∙ cong evaluatePresented p ∙ sym (normalization-evaluation g))

-- yes 的载荷是原 presentation 中的等式；no 的载荷是该等式
-- 导致矛盾的函数。因而正、负结果都带证书，不只是布尔猜测。
-- 判定的是有限 Δ 词模原始 WordRelation 的相等，不是任意图的
-- 弱等价，也不是 DHH、局部化映射空间或同伦群的通用判定器。
wordEquality? : {m n : ℕ} (f g : DeltaWord m n) → Dec (SQ.[ f ] ≡ SQ.[ g ])
wordEquality? f g with normalEquality? (normalizeWord f) (normalizeWord g)
... | yes p = yes (normal-equality→word-equality f g p)
... | no np = no (λ p → np (word-equality→normal-equality f g p))

-- 增量计算：已有 f 的范式时，可以直接继续处理 g，不必重读 f。
normalize-compose : {m n k : ℕ} (f : DeltaWord m n) (g : DeltaWord n k)
  → normalizeWord (seqW f g) ≡ appendWord (normalizeWord f) g
normalize-compose f g = refl

-- 规范化已经规范化的词，不改变范式。
normalize-normalWord : {m n : ℕ} (q : Normal m n)
  → normalizeWord (normalWord q) ≡ q
normalize-normalWord q = normal-semantic-injective _ q
  (normalization-evaluation (normalWord q) ∙ normal-word-evaluation q)

-- 以下例子以 refl 检查判定器实际归约的分支，而不是只复述定理。
-- 每个 true/false 分支仍分别由 wordEquality? 携带上述正/负证书。
decisionTag : {ℓ : Level} {A : Type ℓ} → Dec A → Bool
decisionTag (yes _) = true
decisionTag (no _) = false

example-cancel : decisionTag
  (wordEquality? (seqW (faceW {n = 0} fzero) (degenW fzero)) idW) ≡ true
example-cancel = refl

example-distinct-vertices : decisionTag
  (wordEquality? (faceW {n = 0} fzero) (faceW (fsuc fzero))) ≡ false
example-distinct-vertices = refl

example-interchange : decisionTag
  (wordEquality?
    (seqW (faceW {n = 0} (fsuc fzero)) (faceW fzero))
    (seqW (faceW {n = 0} fzero) (faceW (fsuc (fsuc fzero))))) ≡ true
example-interchange = refl
