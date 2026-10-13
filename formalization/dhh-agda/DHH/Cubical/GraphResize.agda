{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.GraphResize where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Padding
open import DHH.Cubical.GraphCoend

-- 任意带完整端点/min/max证书的区间操作，诱导实际图 coend 的
-- 网格大小变换。来源预层可无限，程序不枚举其 cell 或商顶点。
resizeGraph : {ℓ : Level} {r s : ℕ} (M : IntervalMorph r s) (A : CubicalSet ℓ)
  → Hom (Γₘ r A) (Γₘ s A)
resizeGraph {r = r} {s = s} M A = GraphCoend.fromNerveMap r A (Γₘ s A)
  (GraphCoend.unit s A ⋆n changeSize M (Γₘ s A))

resize-on-grid : {ℓ : Level} {r s : ℕ} (M : IntervalMorph r s) (A : CubicalSet ℓ)
  (n : ℕ) (c : Cell A n)
  → resizeGraph M A ∘g GraphCoend.includeGrid r A n c
    ≡ GraphCoend.includeGrid s A n c ∘g mapGrid M n
resize-on-grid M A n c = homExt (λ _ → refl)

-- 自然性在预层参数上成立：先重命名 cell 再缩网格，等于先缩
-- 网格再重命名。沿商生成元的归纳覆盖整个 Γ，不选择代表。
resize-natural : {ℓ ℓ' : Level} {r s : ℕ} (M : IntervalMorph r s)
  {A : CubicalSet ℓ} {B : CubicalSet ℓ'} (f : CubicalNatural A B)
  → Γₘ-map s f ∘g resizeGraph M A ≡ resizeGraph M B ∘g Γₘ-map r f
resize-natural {r = r} {s = s} M {A} {B} f =
  GraphCoend.Interpret.factor-unique r A (Γₘ s B)
    (f ⋆n GraphCoend.unit s B ⋆n changeSize M (Γₘ s B))
    (Γₘ-map s f ∘g resizeGraph M A)
    (λ n c → homExt (λ _ → refl))
  ∙ sym (GraphCoend.Interpret.factor-unique r A (Γₘ s B)
    (f ⋆n GraphCoend.unit s B ⋆n changeSize M (Γₘ s B))
    (resizeGraph M B ∘g Γₘ-map r f)
    (λ n c → homExt (λ _ → refl)))

-- 两路都由生成格点 (n,c,x) ↦ (n,f(c),M(x)) 唯一确定。
-- factor-unique 把这条程序级等式提升为整个商图上的等式。

resize-identity : {ℓ : Level} (m : ℕ) (A : CubicalSet ℓ)
  → resizeGraph (identityMorph m) A ≡ idHom (Γₘ m A)
resize-identity m A = homExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ { (n , c , x) → cong (GraphCoend.point m A n c)
    (cong (λ h → onVertices h x) (mapGrid-identity m n)) }))

resize-compose : {ℓ : Level} {r s t : ℕ}
  (M : IntervalMorph r s) (N : IntervalMorph s t) (A : CubicalSet ℓ)
  → resizeGraph (composeMorph M N) A ≡ resizeGraph N A ∘g resizeGraph M A
resize-compose {t = t} M N A = homExt (SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ { (n , c , x) → cong (GraphCoend.point t A n c)
    (cong (λ h → onVertices h x) (mapGrid-compose M N n)) }))
