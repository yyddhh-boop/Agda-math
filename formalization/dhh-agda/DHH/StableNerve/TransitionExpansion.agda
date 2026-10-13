{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.TransitionExpansion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.FiniteInterval using (UnitInterval)
open import DHH.Cubes using (Position; here; there; boxHom)
open import DHH.StableNerve.Interval
open import DHH.StableNerve.IntervalLaws using (left-endpoint; right-endpoint)
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Transitions

-- CK 2202.03516v3 §4.8–4.12 的实际局部扩张计算。true 表示 l，
-- false 表示 r；将较短区间以原数值嵌入较长区间，不反射编号。
lowEmbed : {m : ℕ} → Fin (suc m) → Fin (suc (suc m))
lowEmbed fzero = fzero
lowEmbed {suc m} (fsuc x) = fsuc (lowEmbed x)

low-near : {m : ℕ} {x y : Fin (suc m)} → Near x y
  → Near (lowEmbed x) (lowEmbed y)
low-near {x = fzero} {fzero} e = tt
low-near {suc m} {fzero} {fsuc fzero} e = tt
low-near {suc m} {fzero} {fsuc (fsuc y)} ()
low-near {suc m} {fsuc fzero} {fzero} e = tt
low-near {suc m} {fsuc (fsuc x)} {fzero} ()
low-near {suc m} {fsuc x} {fsuc y} e = low-near {m} {x} {y} e

lowMap : (m : ℕ) → Hom (Iₘ m) (Iₘ (suc m))
onVertices (lowMap m) = lowEmbed
preserves (lowMap m) {x} {y} = low-near {m} {x} {y}

sideMorph : (b : Bool) (m : ℕ) → IntervalMorph (suc m) m
sideMorph true = leftMorph
sideMorph false = rightMorph

shiftMap : (b : Bool) (m : ℕ) → Hom (Iₘ (suc m)) (Iₘ (suc m))
shiftMap b m = lowMap m ∘g intervalMap (sideMorph b m)

low-next : {m : ℕ} (x : Fin (suc m)) → Near (lowEmbed x) (fsuc x)
low-next fzero = tt
low-next {suc m} (fsuc x) = low-next x

left-close : {m : ℕ} (x : Fin (suc (suc m)))
  → Near (lowEmbed (leftCollapse x)) x
left-close fzero = tt
left-close (fsuc x) = low-next x

right-close : {m : ℕ} (x : Fin (suc (suc m)))
  → Near (lowEmbed (rightCollapse x)) x
right-close fzero = tt
right-close {zero} (fsuc fzero) = tt
right-close {suc m} (fsuc x) = right-close x

shift-close : (b : Bool) (m : ℕ) (x : Fin (suc (suc m)))
  → Near (onVertices (shiftMap b m) x) x
shift-close true m = left-close
shift-close false m = right-close

recover : (b : Bool) (m : ℕ) → Bool → Fin (suc (suc m)) → Fin (suc (suc m))
recover b m false = onVertices (shiftMap b m)
recover b m true = λ x → x

recover-spatial : (b : Bool) (m : ℕ) (t : Bool)
  {x y : Fin (suc (suc m))} → Near x y → Near (recover b m t x) (recover b m t y)
recover-spatial b m false e = preserves (shiftMap b m) e
recover-spatial b m true e = e

recover-time : (b : Bool) (m : ℕ) (t u : Bool) (x : Fin (suc (suc m)))
  → Near (recover b m t x) (recover b m u x)
recover-time b m false false x = near-refl (recover b m false x)
recover-time b m false true x = shift-close b m x
recover-time b m true false x = near-sym {m = suc m} {x = recover b m false x} {y = x} (shift-close b m x)
recover-time b m true true x = near-refl x

-- 时间变动只使特殊坐标移动至相邻值；空间变动复用实际 shiftMap。
-- 因而这是 BOX 图同态，未使用允许多坐标同时变化的图乘积。
oneStep : (b : Bool) (m : ℕ) → Hom (UnitInterval BOX Iₘ (suc m)) (Iₘ (suc m))
onVertices (oneStep b m) (t , x) = recover b m t x
preserves (oneStep b m) {x = t , x} {y = u , y} = PT.rec
  (near-prop {m = suc m} (recover b m t x) (recover b m u y)) λ where
  (inl (p , e)) → subst (Near (recover b m t x)) (cong (λ v → recover b m v y) p)
    (recover-spatial b m t e)
  (inr (e , p)) → subst (Near (recover b m t x)) (cong (recover b m u) p)
    (recover-time b m t u x)

gate : (b : Bool) (m : ℕ) → Hom (Iₘ (suc m)) UnitInterval
onVertices (gate true m) = threshold (top m)
onVertices (gate false m) = threshold fzero
preserves (gate b m) e = tt

gate-endpoint : (b : Bool) (m : ℕ) (t : Bool)
  → onVertices (gate b m) (endpoint (suc m) t) ≡ t
gate-endpoint true m t = threshold-endpoint (top m) t
gate-endpoint false m t = threshold-endpoint fzero t

-- m+1 长的参数区间在 l 侧最后一步、r 侧第一步切换。
longStep : (b : Bool) (m : ℕ) → Hom (Iₘ (suc m) BOX Iₘ (suc m)) (Iₘ (suc m))
longStep b m = oneStep b m ∘g boxHom (gate b m) (idHom (Iₘ (suc m)))

MixedTarget : (m : ℕ) {n : ℕ} → Position (suc n) → Graph ℓ-zero
MixedTarget m {n} here = Iₘ (suc m) BOX Grid m n
MixedTarget m {suc n} (there i) = Iₘ (suc m) BOX MixedTarget m i

mixedStart mixedEnd : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  → Hom (Grid (suc m) (suc n)) (MixedTarget m i)
mixedStart b m {n} here = boxHom (shiftMap b m) (mapGrid (sideMorph b m) n)
mixedStart b m {suc n} (there i) = boxHom (idHom (Iₘ (suc m))) (mixedStart b m i)
mixedEnd b m {n} here = boxHom (idHom (Iₘ (suc m))) (mapGrid (sideMorph b m) n)
mixedEnd b m {suc n} (there i) = boxHom (idHom (Iₘ (suc m))) (mixedEnd b m i)

mixedValue : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  → Bool → Vertex (Grid (suc m) (suc n)) → Vertex (MixedTarget m i)
mixedValue b m {n} here t (a , x) = recover b m t a , onVertices (mapGrid (sideMorph b m) n) x
mixedValue b m {suc n} (there i) t (a , x) = a , mixedValue b m i t x

mixed-spatial : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n)) (t : Bool)
  {x y : Vertex (Grid (suc m) (suc n))} → Adj (Grid (suc m) (suc n)) x y
  → Adj (MixedTarget m i) (mixedValue b m i t x) (mixedValue b m i t y)
mixed-spatial b m {n} here t {x = a , x} {y = a' , y} = PT.rec (adj-isProp (MixedTarget m {n = n} here) _ _) λ where
  (inl (p , e)) → ∣ inl (cong (recover b m t) p , preserves (mapGrid (sideMorph b m) n) e) ∣₁
  (inr (e , p)) → ∣ inr (recover-spatial b m t e , cong (onVertices (mapGrid (sideMorph b m) n)) p) ∣₁
mixed-spatial b m {suc n} (there i) t {x = a , x} {y = a' , y} = PT.rec (adj-isProp (MixedTarget m (there i)) _ _) λ where
  (inl (p , e)) → ∣ inl (p , mixed-spatial b m i t e) ∣₁
  (inr (e , p)) → ∣ inr (e , cong (mixedValue b m i t) p) ∣₁

mixed-time : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n)) (t u : Bool)
  (x : Vertex (Grid (suc m) (suc n)))
  → Adj (MixedTarget m i) (mixedValue b m i t x) (mixedValue b m i u x)
mixed-time b m here t u (a , x) = ∣ inr (recover-time b m t u a , refl) ∣₁
mixed-time b m {suc n} (there i) t u (a , x) = ∣ inl (refl , mixed-time b m i t u x) ∣₁

mixedOneStep : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  → Hom (UnitInterval BOX Grid (suc m) (suc n)) (MixedTarget m i)
onVertices (mixedOneStep b m i) (t , x) = mixedValue b m i t x
preserves (mixedOneStep b m i) {x = t , x} {y = u , y} = PT.rec (adj-isProp (MixedTarget m i) _ _) λ where
  (inl (p , e)) → subst (Adj (MixedTarget m i) (mixedValue b m i t x))
    (cong (λ v → mixedValue b m i v y) p) (mixed-spatial b m i t e)
  (inr (e , p)) → subst (Adj (MixedTarget m i) (mixedValue b m i t x))
    (cong (mixedValue b m i u) p) (mixed-time b m i t u x)

-- 任意维数/位置的实际混合网格扩张。参数坐标暂放首位，
-- GridFocus 可将它搬到原文最后一位；没有把长度细化当作加维。
mixedExpansion : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  → Hom (Grid (suc m) (suc (suc n))) (MixedTarget m i)
mixedExpansion b m {n} i = mixedOneStep b m i
  ∘g boxHom (gate b m) (idHom (Grid (suc m) (suc n)))

mixedValue-start : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  (x : Vertex (Grid (suc m) (suc n)))
  → mixedValue b m i false x ≡ onVertices (mixedStart b m i) x
mixedValue-start b m here x = refl
mixedValue-start b m {suc n} (there i) (a , x) = cong (a ,_) (mixedValue-start b m i x)

mixedValue-end : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  (x : Vertex (Grid (suc m) (suc n)))
  → mixedValue b m i true x ≡ onVertices (mixedEnd b m i) x
mixedValue-end b m here x = refl
mixedValue-end b m {suc n} (there i) (a , x) = cong (a ,_) (mixedValue-end b m i x)

mixedExpansion-start : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  → mixedExpansion b m i ∘g gridFace (suc m) {n = suc n} here false ≡ mixedStart b m i
mixedExpansion-start b m {n} i = homExt
  {G = Grid (suc m) (suc n)} {H = MixedTarget m {n = n} i}
  {f = mixedExpansion b m {n} i ∘g gridFace (suc m) {n = suc n} here false}
  {g = mixedStart b m {n} i} λ x →
  cong (λ t → mixedValue b m i t x) (gate-endpoint b m false) ∙ mixedValue-start b m i x

mixedExpansion-end : (b : Bool) (m : ℕ) {n : ℕ} (i : Position (suc n))
  → mixedExpansion b m i ∘g gridFace (suc m) {n = suc n} here true ≡ mixedEnd b m i
mixedExpansion-end b m {n} i = homExt
  {G = Grid (suc m) (suc n)} {H = MixedTarget m {n = n} i}
  {f = mixedExpansion b m {n} i ∘g gridFace (suc m) {n = suc n} here true}
  {g = mixedEnd b m {n} i} λ x →
  cong (λ t → mixedValue b m i t x) (gate-endpoint b m true) ∙ mixedValue-end b m i x

-- 实际扩张和两个参数面的完整 Hom 等式已构造。要得到 anodyne，
-- 仍需其余面因子分解、真实 horn 附着 pushout/序列和实现弱比较。
-- 尤其“所有已有面落在旧子对象”不能独自替代 pushout 泛性质。
