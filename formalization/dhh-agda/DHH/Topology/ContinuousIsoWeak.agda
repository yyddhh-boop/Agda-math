{-# OPTIONS --cubical --safe #-}
module DHH.Topology.ContinuousIsoWeak where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
import Cubical.HITs.SetQuotients as SQ
open import DHH.Topology.Base
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.CubicalIso

module IsoWeak {ℓ : Level} (E : CubeGeometry ℓ) where
  open HomotopyGroups E

  module _ {X Y : Top ℓ} (e : ContinuousIso X Y) where
    private
      f = forward e
      g = backward e

    inversePoint : (x : Carrier X) → carrierMap g (carrierMap f x) ≡ x
    inversePoint x = cong (λ h → carrierMap h x) (backward-forward e)

    rightPoint : (y : Carrier Y) → carrierMap f (carrierMap g y) ≡ y
    rightPoint y = cong (λ h → carrierMap h y) (forward-backward e)

    componentsIso : Iso (Components X) (Components Y)
    Iso.fun componentsIso = componentsMap f
    Iso.inv componentsIso = componentsMap g
    Iso.rightInv componentsIso = SQ.elimProp (λ _ → SQ.squash/ _ _)
      (λ y → cong SQ.[_] (rightPoint y))
    Iso.leftInv componentsIso = SQ.elimProp (λ _ → SQ.squash/ _ _)
      (λ x → cong SQ.[_] (inversePoint x))

    -- 回拉基点必须实际调整为 x；不能把 g(f x)=x 当成定义等式。
    -- 同一程序作用于 cube 和 homotopy，固定边界证明随基点等式运输。
    inverseCube : (x : Carrier X) (n : ℕ)
      → BasedCube Y (carrierMap f x) n → BasedCube X x n
    cubeMap (inverseCube x n a) = composeContinuous g (cubeMap a)
    boundary (inverseCube x n a) i b t = cong (carrierMap g) (boundary a i b t) ∙ inversePoint x

    inverseHomotopy : (x : Carrier X) (n : ℕ)
      {a b : BasedCube Y (carrierMap f x) n} → BasedHomotopy a b
      → BasedHomotopy (inverseCube x n a) (inverseCube x n b)
    homotopyMap (inverseHomotopy x n h) = composeContinuous g (homotopyMap h)
    endpoint0 (inverseHomotopy x n h) t = cong (carrierMap g) (endpoint0 h t)
    endpoint1 (inverseHomotopy x n h) t = cong (carrierMap g) (endpoint1 h t)
    fixedBoundary (inverseHomotopy x n h) i b t =
      cong (carrierMap g) (fixedBoundary h i b t) ∙ inversePoint x

    piInverse : (x : Carrier X) (n : ℕ) → Pi Y (carrierMap f x) n → Pi X x n
    piInverse x n = SQ.rec SQ.squash/ (λ a → SQ.[ inverseCube x n a ])
      (λ a b h → SQ.eq/ _ _ (inverseHomotopy x n h))

    piIso : (x : Carrier X) (n : ℕ) → Iso (Pi X x n) (Pi Y (carrierMap f x) n)
    Iso.fun (piIso x n) = piMap f x n
    Iso.inv (piIso x n) = piInverse x n
    Iso.rightInv (piIso x n) = SQ.elimProp (λ _ → SQ.squash/ _ _)
      (λ a → cong SQ.[_] (basedCubeExt (continuousExt (λ t → rightPoint (carrierMap (cubeMap a) t)))))
    Iso.leftInv (piIso x n) = SQ.elimProp (λ _ → SQ.squash/ _ _)
      (λ a → cong SQ.[_] (basedCubeExt (continuousExt (λ t → inversePoint (carrierMap (cubeMap a) t)))))

    continuousIso-isWeak : WeakHomotopyEquivalence f
    components-equiv continuousIso-isWeak = snd (isoToEquiv componentsIso)
    all-pi-equiv continuousIso-isWeak x n = snd (isoToEquiv (piIso x n))

-- 所有正维数和每个基点同时保留，没有用有限阶测试替代全维弱等价。
