{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.UniversalHornReduction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.Kan
open import DHH.Cubical.GraphCoend
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Colimit
import DHH.StableNerve.WholeBoxStages as WS

-- 先证明填充数据可以后合成。程序只对填充 cell 应用 f；
-- 边界证书由 f 的全部立方自然性运输，而非重新求一个 filler。
mapExtension : {ℓ ℓ' : Level} {A : CubicalSet ℓ} {B : CubicalSet ℓ'}
  (f : CubicalNatural A B) {n : ℕ} {missing : Facet n}
  {box : CubicalNatural (OpenBox missing) A}
  → OpenBoxExtension A missing box → OpenBoxExtension B missing (box ⋆n f)
fillingCell (mapExtension f e) = mapCells f _ (fillingCell e)
fillsBox (mapExtension {A = A} {B = B} f {missing = missing} {box = box} e) =
  cubicalNaturalExt λ m c →
    sym (natural f (fst c) (fillingCell e))
    ∙ cong (mapCells f m) (cong (λ h → mapCells h m c) (fillsBox e))

changeExtensionBoundary : {ℓ : Level} {A : CubicalSet ℓ}
  {n : ℕ} {missing : Facet n} {box box' : CubicalNatural (OpenBox missing) A}
  → box ≡ box' → OpenBoxExtension A missing box → OpenBoxExtension A missing box'
fillingCell (changeExtensionBoundary p e) = fillingCell e
fillsBox (changeExtensionBoundary p e) = fillsBox e ∙ p

-- 对每个维数、缺面及网格长度，固定一个“通用的输入图”。
-- 它就是实际余端 Γ_m(horn)，不依赖待填充问题的目标 G。
-- 与有限面节点图的 GraphIso 另见 GraphPresentationComparison。
module Universal {n : ℕ} (missing : Facet n) (k : ℕ) where
  H : Graph ℓ-zero
  H = Γₘ (suc k) (OpenBox missing)

  box : CubicalNatural (OpenBox missing) (N∞ H)
  box = GraphCoend.unit (suc k) (OpenBox missing) ⋆n includeStage H k

  -- 下方归约不假定此 TYPE 有 inhabitant；HornFilling 的实际 Φ、
  -- 全部选面边界与阶段比较另行提供 universalFill 证明项。
  Fill : Type₀
  Fill = OpenBoxExtension (N∞ H) missing box

  interpretBoundary : {ℓ : Level} (G : Graph ℓ)
    (η : CubicalNatural (OpenBox missing) (Nₘ (suc k) G))
    → box ⋆n N∞-map (GraphCoend.fromNerveMap (suc k) (OpenBox missing) G η)
      ≡ η ⋆n includeStage G k
  interpretBoundary G η = cubicalNaturalExt λ d c →
    cong (λ h → mapCells h d (GraphCoend.includeGrid (suc k) (OpenBox missing) d c))
      (N∞-map-on-stage (GraphCoend.fromNerveMap (suc k) (OpenBox missing) G η) k)
    ∙ cong (mapCells (includeStage G k) d)
      (GraphCoend.Interpret.factor-on-grid (suc k) (OpenBox missing) G η d c)

  interpretFill : {ℓ : Level} (G : Graph ℓ)
    (η : CubicalNatural (OpenBox missing) (Nₘ (suc k) G))
    → Fill → OpenBoxExtension (N∞ G) missing (η ⋆n includeStage G k)
  interpretFill G η e = changeExtensionBoundary (interpretBoundary G η)
    (mapExtension (N∞-map (GraphCoend.fromNerveMap (suc k) (OpenBox missing) G η)) e)

UniversalHornFillings : Type₀
UniversalHornFillings = (n : ℕ) (missing : Facet n) (k : ℕ) → ∥ Universal.Fill missing k ∥₁

-- 归约覆盖任意 universe、任意无限图 G 和全部维数。先把完整
-- horn 图式提升到一个阶段，再把通用填充沿实际图同态送入 G。
-- 两次截断消去的目标均为截断存在，不引入选择或可判定性。
universalHornFillings→Kan : UniversalHornFillings
  → {ℓ : Level} (G : Graph ℓ) → IsKan (N∞ G)
universalHornFillings→Kan fills G n missing box =
  PT.rec squash₁ fromStage (WS.GraphStages.openBoxStage G missing box)
  where
  module W = WS.GraphStages.Model.OpenBox G missing

  fromStage : W.WholeStage box → ∥ OpenBoxExtension (N∞ G) missing box ∥₁
  fromStage d = PT.map
    (λ e → changeExtensionBoundary (W.recovers d)
      (Universal.interpretFill missing (W.stage d) G (W.stageMap d) e))
    (fills n missing (W.stage d))
