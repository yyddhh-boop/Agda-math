{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.IntegerStable where

-- 居中窗口的延拓相容使整数模型上的映射真正下降到 N∞ 的集合商。
-- 这里的 WindowStable 是有限居中窗口的稳定性；IntegerPaperStability
-- 另以有限维归纳证明它与文献逐方向稳定性等价，而非靠命名替代比较。

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; left-≤-max; right-≤-max)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation.Properties as PT
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubicalNerve
open import DHH.StableNerve.Grid using (Grid)
open import DHH.StableNerve.IntegerInterval
open import DHH.StableNerve.CenteredInterval
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.Colimit
open import DHH.StableNerve.StageArithmetic using (Later; now; next; fromLe)
open import DHH.StableNerve.CommonStage

private variable ℓ ℓ' : Level

centeredExtend : {G : Graph ℓ} (k n : ℕ)
  → Hom (Grid (suc k) n) G → Hom (IntegerGrid n) G
centeredExtend k n f = f ∘g centeredClampGrid k n

centeredRestrict : {G : Graph ℓ} (k n : ℕ)
  → Hom (IntegerGrid n) G → Hom (Grid (suc k) n) G
centeredRestrict k n f = f ∘g centeredGridInclusion k n

centered-restrict-extend : {G : Graph ℓ} (k n : ℕ) (f : Hom (Grid (suc k) n) G)
  → centeredRestrict k n (centeredExtend k n f) ≡ f
centered-restrict-extend k n f = homExt λ x →
  cong (onVertices f) (centeredGrid-retraction-point k n x)

centeredExtend-injective : {G : Graph ℓ} (k n : ℕ) {f g : Hom (Grid (suc k) n) G}
  → centeredExtend k n f ≡ centeredExtend k n g → f ≡ g
centeredExtend-injective k n {f} {g} p =
  sym (centered-restrict-extend k n f)
    ∙ cong (centeredRestrict k n) p ∙ centered-restrict-extend k n g

choose-extension-step : {G : Graph ℓ} (b : Bool) (a m n : ℕ)
  (f : Hom (Grid m n) G)
  → mapCells (chooseTransition b m G) n f ∘g shiftedClampGrid (shiftNext b a) (suc m) n
    ≡ f ∘g shiftedClampGrid a m n
choose-extension-step true a m n f = homExt λ x →
  cong (onVertices f) (shifted-grid-clamp-step true a m n x)
choose-extension-step false a m n f = homExt λ x →
  cong (onVertices f) (shifted-grid-clamp-step false a m n x)

centered-extension-step : {G : Graph ℓ} (k n : ℕ) (f : Hom (Grid (suc k) n) G)
  → centeredExtend (suc k) n (mapCells (stageTransition G k) n f)
    ≡ centeredExtend k n f
centered-extension-step k n f =
  choose-extension-step (evenStage k) (offset k) (suc k) n f

windowProjection : (k n : ℕ) → Hom (IntegerGrid n) (IntegerGrid n)
windowProjection k n = centeredGridInclusion k n ∘g centeredClampGrid k n

WindowStable : {G : Graph ℓ} {n : ℕ} → Hom (IntegerGrid n) G → Type ℓ
WindowStable {n = n} f = ∥ Σ[ k ∈ ℕ ] f ∘g windowProjection k n ≡ f ∥₁

StableIntegerCell : (G : Graph ℓ) (n : ℕ) → Type ℓ
StableIntegerCell G n = Σ[ f ∈ Hom (IntegerGrid n) G ] WindowStable {n = n} f

stableIntegerCell-isSet : (G : Graph ℓ) (n : ℕ) → isSet (StableIntegerCell G n)
stableIntegerCell-isSet G n = isSetΣSndProp isSetGraphHom (λ _ → squash₁)

extension-window-stable : {G : Graph ℓ} (k n : ℕ) (f : Hom (Grid (suc k) n) G)
  → WindowStable {n = n} (centeredExtend k n f)
extension-window-stable {G = G} k n f = ∣ k , homExt {G = IntegerGrid n} {H = G} (λ x → cong (onVertices f)
  (centeredGrid-retraction-point k n (onVertices (centeredClampGrid k n) x))) ∣₁

stableIntegerMap : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H) (n : ℕ)
  → StableIntegerCell G n → StableIntegerCell H n
stableIntegerMap h n (f , p) = h ∘g f , PT.rec squash₁
  (λ { (k , e) → ∣ k , homExt (λ x →
    cong (onVertices h) (cong (λ g → onVertices g x) e)) ∣₁ }) p

module IntegerComparison {ℓ : Level} (G : Graph ℓ) where
  module K = CommonStages (Stage G) (stageTransition G)

  -- 商消去的关键只用已证的一步相容，不要求任何未定义的弱等价。
  integerHom : (n : ℕ) → Cell (N∞ G) n → Hom (IntegerGrid n) G
  integerHom n = SQ.rec isSetGraphHom
    (λ { (k , f) → centeredExtend k n f })
    (λ { (k , f) .(suc k , mapCells (stageTransition G k) n f) (Stable.step f)
      → sym (centered-extension-step k n f) })

  integerHom-on-stage : (k n : ℕ) (f : Hom (Grid (suc k) n) G)
    → integerHom n (mapCells (includeStage G k) n f) ≡ centeredExtend k n f
  integerHom-on-stage k n f = refl

  integerHom-stable : (n : ℕ) (c : Cell (N∞ G) n) → WindowStable {n = n} (integerHom n c)
  integerHom-stable n = SQ.elimProp (λ _ → squash₁)
    (λ { (k , f) → extension-window-stable k n f })

  integerCell : (n : ℕ) → Cell (N∞ G) n → StableIntegerCell G n
  integerCell n c = integerHom n c , integerHom-stable n c

  extension-later : {k l : ℕ} (p : Later k l) (n : ℕ) (f : Hom (Grid (suc k) n) G)
    → centeredExtend l n (mapCells (K.laterMap p) n f) ≡ centeredExtend k n f
  extension-later now n f = refl
  extension-later (next {l} p) n f =
    centered-extension-step l n (mapCells (K.laterMap p) n f) ∙ extension-later p n f

  extension-advance : {k l : ℕ} (p : k ≤ l) (n : ℕ) (f : Hom (Grid (suc k) n) G)
    → centeredExtend l n (K.advanceCell p n f) ≡ centeredExtend k n f
  extension-advance p = extension-later (fromLe p)

  -- 两个阶段的无限延拓若完全相等，就在 max(k,l) 阶段相等。
  -- 取有限共同阶段后，由有限窗口回缩消去延拓；没有可数选择。
  extension-equality : (n k l : ℕ)
    (f : Hom (Grid (suc k) n) G) (g : Hom (Grid (suc l) n) G)
    → centeredExtend k n f ≡ centeredExtend l n g
    → mapCells (includeStage G k) n f ≡ mapCells (includeStage G l) n g
  extension-equality n k l f g p = K.common-to-equality n (k , f) (l , g)
    ∣ max k l , left-≤-max , right-≤-max ,
      centeredExtend-injective (max k l) n
        (extension-advance left-≤-max n f ∙ p
          ∙ sym (extension-advance right-≤-max n g)) ∣₁

  integerHom-injective : (n : ℕ) (c d : Cell (N∞ G) n)
    → integerHom n c ≡ integerHom n d → c ≡ d
  integerHom-injective n = SQ.elimProp (λ c → isPropΠ2 (λ d _ → SQ.squash/ c d))
    (λ { (k , f) → SQ.elimProp (λ d → isPropΠ (λ _ → SQ.squash/ _ d))
      (λ { (l , g) → extension-equality n k l f g }) })

  -- 不从截断中任意挑阶段。先证明比较映射的每个纤维为命题，
  -- 再消去稳定窗口存在性的截断，得到唯一的 colimit cell。
  IntegerFiber : (n : ℕ) (f : Hom (IntegerGrid n) G) → Type ℓ
  IntegerFiber n f = Σ[ c ∈ Cell (N∞ G) n ] integerHom n c ≡ f

  integerFiber-isProp : (n : ℕ) (f : Hom (IntegerGrid n) G) → isProp (IntegerFiber n f)
  integerFiber-isProp n f (c , p) (d , q) = Σ≡Prop
    (λ _ → isSetGraphHom _ _)
    (integerHom-injective n c d (p ∙ sym q))

  stable-fiber : (n : ℕ) (f : Hom (IntegerGrid n) G) → WindowStable {n = n} f → IntegerFiber n f
  stable-fiber n f = PT.rec (integerFiber-isProp n f) λ { (k , p) →
    mapCells (includeStage G k) n (centeredRestrict k n f) , p }

  stableToColimit : (n : ℕ) → StableIntegerCell G n → Cell (N∞ G) n
  stableToColimit n (f , p) = fst (stable-fiber n f p)

  integerCellIso : (n : ℕ) → Iso (Cell (N∞ G) n) (StableIntegerCell G n)
  Iso.fun (integerCellIso n) = integerCell n
  Iso.inv (integerCellIso n) = stableToColimit n
  Iso.rightInv (integerCellIso n) (f , p) = Σ≡Prop (λ _ → squash₁)
    (snd (stable-fiber n f p))
  Iso.leftInv (integerCellIso n) c = integerHom-injective n _ c
    (snd (stable-fiber n (integerHom n c) (integerHom-stable n c)))

  integerCellEquivalence : (n : ℕ) → Cell (N∞ G) n ≃ StableIntegerCell G n
  integerCellEquivalence n = isoToEquiv (integerCellIso n)

-- 图映射只做后复合，故比较与它严格相容。这是实际商上的等式，
-- 不是仅比较所挑代表元，也不要求 G/H 在同一 universe level。
integerHom-natural : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H) (n : ℕ)
  (c : Cell (N∞ G) n)
  → IntegerComparison.integerHom H n (mapCells (N∞-map h) n c)
    ≡ h ∘g IntegerComparison.integerHom G n c
integerHom-natural h n = SQ.elimProp (λ _ → isSetGraphHom _ _)
  (λ { (k , f) → homExt (λ _ → refl) })

integerCell-natural : {G : Graph ℓ} {H : Graph ℓ'} (h : Hom G H) (n : ℕ)
  (c : Cell (N∞ G) n)
  → IntegerComparison.integerCell H n (mapCells (N∞-map h) n c)
    ≡ stableIntegerMap h n (IntegerComparison.integerCell G n c)
integerCell-natural h n c = Σ≡Prop (λ _ → squash₁) (integerHom-natural h n c)
