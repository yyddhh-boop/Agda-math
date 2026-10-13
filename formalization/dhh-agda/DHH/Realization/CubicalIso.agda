{-# OPTIONS --cubical --safe #-}
module DHH.Realization.CubicalIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.CubicalNerve
open import DHH.PresheafInterop
open import DHH.Topology.Base
open import DHH.Realization.Coend
open import DHH.CubeCategory

private variable ℓ : Level

-- 双向连续、严格互逆；这是比弱同伦等价更强的比较数据。
record ContinuousIso (X Y : Top ℓ) : Type (ℓ-suc ℓ) where
  field
    forward : Continuous X Y
    backward : Continuous Y X
    backward-forward : composeContinuous backward forward ≡ identityContinuous X
    forward-backward : composeContinuous forward backward ≡ identityContinuous Y
open ContinuousIso public

continuousCarrierIso : {X Y : Top ℓ} → ContinuousIso X Y → Iso (Carrier X) (Carrier Y)
Iso.fun (continuousCarrierIso e) = carrierMap (forward e)
Iso.inv (continuousCarrierIso e) = carrierMap (backward e)
Iso.rightInv (continuousCarrierIso e) y = cong (λ f → carrierMap f y) (forward-backward e)
Iso.leftInv (continuousCarrierIso e) x = cong (λ f → carrierMap f x) (backward-forward e)

module CubicalRealization {ℓ : Level} (D : DiskDiagram CubeCategory ℓ) where
  module R (A : CubicalSet ℓ) = Realization D (asPresheaf A)

  realizeCubical : CubicalSet ℓ → Top ℓ
  realizeCubical A = R.realize A isSetℕ

  realizeCubicalMap : {A B : CubicalSet ℓ} → CubicalNatural A B
    → Continuous (realizeCubical A) (realizeCubical B)
  realizeCubicalMap η = RealizationMap.realizeMap isSetℕ D (asNaturalTransformation η)

  -- 一次定义在生成 cell 上，再利用集合商的命题消去证明全空间等式。
  -- 这是“组合构造正确性跟着递归/商生成元走”的一个可复用模板。
  realizeCubical-id : (A : CubicalSet ℓ)
    → realizeCubicalMap (cubicalId A) ≡ identityContinuous (realizeCubical A)
  realizeCubical-id A = continuousExt
    (SQ.elimProp (λ _ → carrier-isSet (realizeCubical A) _ _) (λ _ → refl))

  realizeCubical-compose : {A B C : CubicalSet ℓ}
    (f : CubicalNatural A B) (g : CubicalNatural B C)
    → realizeCubicalMap (f ⋆n g)
      ≡ composeContinuous (realizeCubicalMap g) (realizeCubicalMap f)
  realizeCubical-compose {C = C} f g = continuousExt
    (SQ.elimProp (λ _ → carrier-isSet (realizeCubical C) _ _) (λ _ → refl))

  realizeCubicalIso : {A B : CubicalSet ℓ}
    (f : CubicalNatural A B) (g : CubicalNatural B A)
    → f ⋆n g ≡ cubicalId A → g ⋆n f ≡ cubicalId B
    → ContinuousIso (realizeCubical A) (realizeCubical B)
  forward (realizeCubicalIso f g p q) = realizeCubicalMap f
  backward (realizeCubicalIso f g p q) = realizeCubicalMap g
  backward-forward (realizeCubicalIso {A = A} f g p q) =
    sym (realizeCubical-compose f g) ∙ cong realizeCubicalMap p ∙ realizeCubical-id A
  forward-backward (realizeCubicalIso {B = B} f g p q) =
    sym (realizeCubical-compose g f) ∙ cong realizeCubicalMap q ∙ realizeCubical-id B

  realizeCubicalCarrierEquivalence : {A B : CubicalSet ℓ}
    (f : CubicalNatural A B) (g : CubicalNatural B A)
    → f ⋆n g ≡ cubicalId A → g ⋆n f ≡ cubicalId B
    → Carrier (realizeCubical A) ≃ Carrier (realizeCubical B)
  realizeCubicalCarrierEquivalence f g p q = isoToEquiv
    (continuousCarrierIso (realizeCubicalIso f g p q))

-- 仅 cell 集合逐阶等价不足够：输入必须包括两个自然变换及它们的
-- 全预层互逆等式。故不能忽略 faces/connections 后调用本定理。
