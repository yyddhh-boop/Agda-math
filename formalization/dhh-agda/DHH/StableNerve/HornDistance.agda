{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.HornDistance where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; +-zero; +-comm)
open import Cubical.Data.Nat.Properties using (zero∸; ∸+)
open import Cubical.Data.FinData using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
open import DHH.StableNerve.Interval using (Near; near-refl; near-sym; top; endpoint)
open import DHH.StableNerve.IntegerClamp using (clampNat; clamp-at-or-above)
open import DHH.StableNerve.HornScalar
open import DHH.StableNerve.HornInterval using (clampNat-zero)

-- 参数 a 是左 padding，b 是中间窗口宽度。按 a 和输入 v 共同
-- 剥离后继，程序直接给出坐标与窗口外距离，不搜索顶点列表。
windowCoordinate : (a b v : ℕ) → Fin (suc b)
windowCoordinate zero b v = clampNat b v
windowCoordinate (suc a) b zero = fzero
windowCoordinate (suc a) b (suc v) = windowCoordinate a b v

windowDistance : ℕ → ℕ → ℕ → ℕ
windowDistance zero b v = v ∸ b
windowDistance (suc a) b zero = suc a
windowDistance (suc a) b (suc v) = windowDistance a b v

-- 这两条识别把递归代码接回原收缩的算式；不是另选一种距离。
coordinate-formula : (a b v : ℕ)
  → windowCoordinate a b v ≡ clampNat b (v ∸ a)
coordinate-formula zero b v = refl
coordinate-formula (suc a) b zero = refl
coordinate-formula (suc a) b (suc v) = coordinate-formula a b v

distance-formula : (a b v : ℕ)
  → windowDistance a b v ≡ (a ∸ v) + (v ∸ (a + b))
distance-formula zero b zero = refl
distance-formula zero b (suc v) = refl
distance-formula (suc a) b zero = sym (+-zero (suc a))
distance-formula (suc a) b (suc v) = distance-formula a b v

coordinate-zero : (a b : ℕ) → windowCoordinate a b zero ≡ fzero
coordinate-zero zero b = refl
coordinate-zero (suc a) b = refl

distance-zero-input : (a b : ℕ) → windowDistance a b zero ≡ a
distance-zero-input zero b = zero∸ b
distance-zero-input (suc a) b = refl

coordinate-shift : (a b v : ℕ)
  → windowCoordinate a b (a + v) ≡ clampNat b v
coordinate-shift zero b v = refl
coordinate-shift (suc a) b v = coordinate-shift a b v

distance-shift : (a b v : ℕ)
  → windowDistance a b (a + v) ≡ v ∸ b
distance-shift zero b v = refl
distance-shift (suc a) b v = distance-shift a b v

coordinate-right : (a b t : ℕ)
  → windowCoordinate a b (a + (b + t)) ≡ top b
coordinate-right a b t = coordinate-shift a b (b + t) ∙ clamp-at-or-above b t

distance-right : (a b t : ℕ)
  → windowDistance a b (a + (b + t)) ≡ t
distance-right a b t = distance-shift a b (b + t) ∙ ∸+ t b

nearNat-sym : {x y : ℕ} → NearNat x y → NearNat y x
nearNat-sym {zero} {zero} e = e
nearNat-sym {zero} {suc y} e = e
nearNat-sym {suc x} {zero} e = e
nearNat-sym {suc x} {suc y} e = nearNat-sym {x} {y} e

-- 将相邻证书展开为相等、正向一步或反向一步，剥离共同后继。
-- 此处输出有限的结构分支，不判定商图中的任意相等。
NearCases : ℕ → ℕ → Type₀
NearCases x y = (x ≡ y) ⊎ ((suc x ≡ y) ⊎ (x ≡ suc y))

nearCases : {x y : ℕ} → NearNat x y → NearCases x y
nearCases {zero} {zero} e = inl refl
nearCases {zero} {suc zero} e = inr (inl refl)
nearCases {zero} {suc (suc y)} ()
nearCases {suc zero} {zero} e = inr (inr refl)
nearCases {suc (suc x)} {zero} ()
nearCases {suc x} {suc y} e with nearCases {x} {y} e
... | inl p = inl (cong suc p)
... | inr (inl p) = inr (inl (cong suc p))
... | inr (inr p) = inr (inr (cong suc p))

-- 关键不变量：边处于某个共同端点，或者两端距离都是零。
-- 仅知道两个距离相邻是不够的，因为 Φ 还要进入同一个生成面。
data WindowEdge (a b v w : ℕ) : Type₀ where
  leftEdge : windowCoordinate a b v ≡ fzero
    → windowCoordinate a b w ≡ fzero
    → NearNat (windowDistance a b v) (windowDistance a b w)
    → WindowEdge a b v w
  rightEdge : windowCoordinate a b v ≡ top b
    → windowCoordinate a b w ≡ top b
    → NearNat (windowDistance a b v) (windowDistance a b w)
    → WindowEdge a b v w
  middleEdge : windowDistance a b v ≡ zero
    → windowDistance a b w ≡ zero
    → Near (windowCoordinate a b v) (windowCoordinate a b w)
    → WindowEdge a b v w

-- 左 padding 为零时只需右端/中间两支；保留这个更精确的类型
-- 让增加窗口宽度的归纳无需排除“从未产生”的左端分支。
data InitialEdge (b v w : ℕ) : Type₀ where
  initialRight : clampNat b v ≡ top b → clampNat b w ≡ top b
    → NearNat (v ∸ b) (w ∸ b) → InitialEdge b v w
  initialMiddle : v ∸ b ≡ zero → w ∸ b ≡ zero
    → Near (clampNat b v) (clampNat b w) → InitialEdge b v w

initialNext : (b v : ℕ) → InitialEdge b v (suc v)
initialNext zero v = initialRight (clampNat-zero v) (clampNat-zero (suc v)) (nearNat-next v)
initialNext (suc b) zero = initialMiddle refl (zero∸ b) tt
initialNext (suc b) (suc v) with initialNext b v
... | initialRight p q e = initialRight (cong fsuc p) (cong fsuc q) e
... | initialMiddle p q e = initialMiddle p q e

initialToWindow : {b v w : ℕ} → InitialEdge b v w → WindowEdge zero b v w
initialToWindow (initialRight p q e) = rightEdge p q e
initialToWindow (initialMiddle p q e) = middleEdge p q e

shiftEdge : {a b v w : ℕ} → WindowEdge a b v w
  → WindowEdge (suc a) b (suc v) (suc w)
shiftEdge (leftEdge p q e) = leftEdge p q e
shiftEdge (rightEdge p q e) = rightEdge p q e
shiftEdge (middleEdge p q e) = middleEdge p q e

windowNext : (a b v : ℕ) → WindowEdge a b v (suc v)
windowNext zero b v = initialToWindow (initialNext b v)
windowNext (suc a) b zero = leftEdge refl (coordinate-zero a b)
  (subst (NearNat (suc a)) (sym (distance-zero-input a b)) (nearNat-prev a))
windowNext (suc a) b (suc v) = shiftEdge (windowNext a b v)

windowSelf : (a b v : ℕ) → WindowEdge a b v v
windowSelf a b v with windowNext a b v
... | leftEdge p q e = leftEdge p p (nearNat-refl (windowDistance a b v))
... | rightEdge p q e = rightEdge p p (nearNat-refl (windowDistance a b v))
... | middleEdge p q e = middleEdge p p (near-refl (windowCoordinate a b v))

reverseEdge : {a b v w : ℕ} → WindowEdge a b v w → WindowEdge a b w v
reverseEdge {a} {b} {v} {w} (leftEdge p q e) = leftEdge q p
  (nearNat-sym {windowDistance a b v} {windowDistance a b w} e)
reverseEdge {a} {b} {v} {w} (rightEdge p q e) = rightEdge q p
  (nearNat-sym {windowDistance a b v} {windowDistance a b w} e)
reverseEdge {a} {b} {v} {w} (middleEdge p q e) = middleEdge q p
  (near-sym {m = b} {x = windowCoordinate a b v} {y = windowCoordinate a b w} e)

windowEdge : (a b : ℕ) {v w : ℕ} → NearNat v w → WindowEdge a b v w
windowEdge a b {v} {w} e with nearCases {v} {w} e
... | inl p = subst (WindowEdge a b v) p (windowSelf a b v)
... | inr (inl p) = subst (WindowEdge a b v) p (windowNext a b v)
... | inr (inr p) = subst (λ z → WindowEdge a b z w) (sym p) (reverseEdge (windowNext a b w))

distance-near : (a b : ℕ) {v w : ℕ} → NearNat v w
  → NearNat (windowDistance a b v) (windowDistance a b w)
distance-near a b {v} {w} e with windowEdge a b {v} {w} e
... | leftEdge p q d = d
... | rightEdge p q d = d
... | middleEdge p q c = subst2 NearNat (sym p) (sym q) tt

-- 正距离携带一个端点见证；反过来，真正的内点距离为零。
-- 这些证书将用于高维距离递归取得一个共同选面，不选择商代表。
positive-distance-endpoint : (a b v : ℕ) → (windowDistance a b v ≡ zero → Empty.⊥)
  → Σ[ ε ∈ Bool ] windowCoordinate a b v ≡ endpoint b ε
positive-distance-endpoint a b v nonzero with windowSelf a b v
... | leftEdge p q e = false , p
... | rightEdge p q e = true , p
... | middleEdge p q e = Empty.rec (nonzero p)

interior-distance-zero : (a b v : ℕ)
  → (windowCoordinate a b v ≡ fzero → Empty.⊥)
  → (windowCoordinate a b v ≡ top b → Empty.⊥)
  → windowDistance a b v ≡ zero
interior-distance-zero a b v notLeft notRight with windowSelf a b v
... | leftEdge p q e = Empty.rec (notLeft p)
... | rightEdge p q e = Empty.rec (notRight p)
... | middleEdge p q e = p

-- BOX 边只改变一个坐标；其余距离加数固定。加法分别保相邻
-- 正是把这一局部证书送进总距离 D 所需要的规律。
add-near-left : (t : ℕ) {v w : ℕ} → NearNat v w → NearNat (t + v) (t + w)
add-near-left zero e = e
add-near-left (suc t) {v} {w} e = add-near-left t {v} {w} e

add-near-right : (t : ℕ) {v w : ℕ} → NearNat v w → NearNat (v + t) (w + t)
add-near-right t {v} {w} e = subst2 NearNat (+-comm t v) (+-comm t w) (add-near-left t e)

-- 设置 a=b=m 即得到论文 [m,2m] 窗口的距离；完整 Φ 仍需将
-- 高维输出送入按面生成的 horn 图，并支付边界-stage相容证明。
