{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.WordNormalization where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Categories.Category.Base using (Category)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Cubes using (here)
open import DHH.Simplicial.Word
open import DHH.Simplicial.Presentation
open import DHH.Simplicial.PresentationShift
open import DHH.Simplicial.NormalForm
open import DHH.Simplicial.NormalFormRelations

-- 构造视角：给定有限 DeltaWord，递归折叠语法树得到 Normal。
-- appendFace/appendDegen 的互递归由规范形的子结构和位置参数控制，
-- 终止性由 Agda 检查；没有搜索所有单纯映射，也未给出复杂度上界。
-- 下方 *-sound 与相同递归同步，在原始呈示关系中证明每步保持含义。
mutual
  appendFace : {m n : ℕ} → Normal m n → Fin (suc (suc n)) → Normal m (suc n)
  appendFace (nzero z) fzero = nshift (nzero z)
  appendFace (nzero z) (fsuc i) = nzero (appendZeroFace z i)
  appendFace (nshift q) fzero = nshift (nshift q)
  appendFace (nshift q) (fsuc i) = nshift (appendFace q i)

  appendZeroFace : {m n : ℕ} → ZeroNormal m n → Fin (suc n) → ZeroNormal m (suc n)
  appendZeroFace zvertex i = zvertex
  appendZeroFace (zrepeat z) i = zrepeat (appendZeroFace z i)
  appendZeroFace (zlift q) i = zlift (appendFace q i)

collapseLift : {m n : ℕ} → Normal m n → ZeroNormal (suc m) n
collapseLift (nzero z) = zrepeat z
collapseLift (nshift q) = zlift q

mutual
  appendDegen : {m n : ℕ} → Normal m (suc n) → Fin (suc n) → Normal m n
  appendDegen (nzero z) i = nzero (appendZeroDegen z i)
  appendDegen (nshift q) fzero = q
  appendDegen {n = suc n} (nshift q) (fsuc i) = nshift (appendDegen q i)

  appendZeroDegen : {m n : ℕ} → ZeroNormal m (suc n) → Fin (suc n) → ZeroNormal m n
  appendZeroDegen zvertex i = zvertex
  appendZeroDegen (zrepeat z) i = zrepeat (appendZeroDegen z i)
  appendZeroDegen (zlift q) i = appendLiftDegen q i

  appendLiftDegen : {m n : ℕ} → Normal m n → Fin (suc n) → ZeroNormal (suc m) n
  appendLiftDegen q fzero = collapseLift q
  appendLiftDegen {n = suc n} q (fsuc i) = zlift (appendDegen q i)

-- Every computation is justified in the ORIGINAL presentation quotient.
mutual
  appendFace-sound : {m n : ℕ} (q : Normal m n) (i : Fin (suc (suc n)))
    → SQ.[ normalWord q ] ⋆p SQ.[ faceW i ] ≡ SQ.[ normalWord (appendFace q i) ]
  appendFace-sound (nzero z) fzero = refl
  appendFace-sound (nzero z) (fsuc i) = appendZeroFace-sound z i
  appendFace-sound (nshift q) fzero = refl
  appendFace-sound (nshift q) (fsuc i) =
    Category.⋆Assoc DeltaPresentation SQ.[ normalWord q ] SQ.[ faceW fzero ] SQ.[ faceW (fsuc i) ]
    ∙ cong (SQ.[ normalWord q ] ⋆p_) (head-inclusion-word (faceW i))
    ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ normalWord q ] SQ.[ faceW i ] SQ.[ faceW fzero ])
    ∙ cong (_⋆p SQ.[ faceW fzero ]) (appendFace-sound q i)

  appendZeroFace-sound : {m n : ℕ} (z : ZeroNormal m n) (i : Fin (suc n))
    → SQ.[ zeroWord z ] ⋆p SQ.[ faceW (fsuc i) ] ≡ SQ.[ zeroWord (appendZeroFace z i) ]
  appendZeroFace-sound {n = n} zvertex i = vertex-face n i
  appendZeroFace-sound (zrepeat z) i =
    Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ] SQ.[ zeroWord z ] SQ.[ faceW (fsuc i) ]
    ∙ cong (SQ.[ degenW fzero ] ⋆p_) (appendZeroFace-sound z i)
  appendZeroFace-sound (zlift q) i = cong liftPresented (appendFace-sound q i)

mutual
  appendDegen-sound : {m n : ℕ} (q : Normal m (suc n)) (i : Fin (suc n))
    → SQ.[ normalWord q ] ⋆p SQ.[ degenW i ] ≡ SQ.[ normalWord (appendDegen q i) ]
  appendDegen-sound (nzero z) i = appendZeroDegen-sound z i
  appendDegen-sound (nshift q) fzero =
    Category.⋆Assoc DeltaPresentation SQ.[ normalWord q ] SQ.[ faceW fzero ] SQ.[ degenW fzero ]
    ∙ cong (SQ.[ normalWord q ] ⋆p_) (SQ.eq/ _ _ (same here))
    ∙ Category.⋆IdR DeltaPresentation SQ.[ normalWord q ]
  appendDegen-sound {n = suc n} (nshift q) (fsuc i) =
    Category.⋆Assoc DeltaPresentation SQ.[ normalWord q ] SQ.[ faceW fzero ] SQ.[ degenW (fsuc i) ]
    ∙ cong (SQ.[ normalWord q ] ⋆p_) (head-inclusion-word (degenW i))
    ∙ sym (Category.⋆Assoc DeltaPresentation SQ.[ normalWord q ] SQ.[ degenW i ] SQ.[ faceW fzero ])
    ∙ cong (_⋆p SQ.[ faceW fzero ]) (appendDegen-sound q i)

  appendZeroDegen-sound : {m n : ℕ} (z : ZeroNormal m (suc n)) (i : Fin (suc n))
    → SQ.[ zeroWord z ] ⋆p SQ.[ degenW i ] ≡ SQ.[ zeroWord (appendZeroDegen z i) ]
  appendZeroDegen-sound {n = n} zvertex i = vertex-degen n i
  appendZeroDegen-sound (zrepeat z) i =
    Category.⋆Assoc DeltaPresentation SQ.[ degenW fzero ] SQ.[ zeroWord z ] SQ.[ degenW i ]
    ∙ cong (SQ.[ degenW fzero ] ⋆p_) (appendZeroDegen-sound z i)
  appendZeroDegen-sound (zlift (nzero z)) fzero = zero-shift-collapse z
  appendZeroDegen-sound (zlift (nshift q)) fzero =
    Category.⋆Assoc DeltaPresentation SQ.[ liftWord (normalWord q) ] SQ.[ faceW (fsuc fzero) ] SQ.[ degenW fzero ]
    ∙ cong (SQ.[ liftWord (normalWord q) ] ⋆p_) (SQ.eq/ _ _ (next here))
    ∙ Category.⋆IdR DeltaPresentation SQ.[ liftWord (normalWord q) ]
  appendZeroDegen-sound {n = suc n} (zlift q) (fsuc i) = cong liftPresented (appendDegen-sound q i)

identityNormal : (n : ℕ) → Normal n n
identityNormal zero = nzero zvertex
identityNormal (suc n) = nzero (zlift (identityNormal n))

identityNormal-sound : (n : ℕ) → SQ.[ normalWord (identityNormal n) ] ≡ SQ.[ idW ]
identityNormal-sound zero = refl
identityNormal-sound (suc n) = cong liftPresented (identityNormal-sound n)

appendWord : {m n k : ℕ} → Normal m n → DeltaWord n k → Normal m k
appendWord q idW = q
appendWord q (faceW i) = appendFace q i
appendWord q (degenW i) = appendDegen q i
appendWord q (seqW f g) = appendWord (appendWord q f) g

appendWord-sound : {m n k : ℕ} (q : Normal m n) (w : DeltaWord n k)
  → SQ.[ normalWord q ] ⋆p SQ.[ w ] ≡ SQ.[ normalWord (appendWord q w) ]
appendWord-sound q idW = Category.⋆IdR DeltaPresentation SQ.[ normalWord q ]
appendWord-sound q (faceW i) = appendFace-sound q i
appendWord-sound q (degenW i) = appendDegen-sound q i
appendWord-sound q (seqW f g) =
  sym (Category.⋆Assoc DeltaPresentation SQ.[ normalWord q ] SQ.[ f ] SQ.[ g ])
  ∙ cong (_⋆p SQ.[ g ]) (appendWord-sound q f)
  ∙ appendWord-sound (appendWord q f) g

-- 输入是一个有限带型语法表达式；输出是其规范形。
-- word-normalization 给出原表达式等于规范形的证明；语义单射及
-- 呈示忠实性的后续推论见 NormalForm 与 PresentationCompleteness。
normalizeWord : {m n : ℕ} → DeltaWord m n → Normal m n
normalizeWord {m = m} w = appendWord (identityNormal m) w

word-normalization : {m n : ℕ} (w : DeltaWord m n)
  → SQ.[ w ] ≡ SQ.[ normalWord (normalizeWord w) ]
word-normalization {m = m} w =
  sym (Category.⋆IdL DeltaPresentation SQ.[ w ])
  ∙ cong (_⋆p SQ.[ w ]) (sym (identityNormal-sound m))
  ∙ appendWord-sound (identityNormal m) w
