{-# OPTIONS --cubical --safe #-}
module DHH.StableNerve.Colimit where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Categories.Functor.Base using (Functor)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.GraphSets
open import DHH.CubicalNerve
open import DHH.StableNerve.Nerve
open import DHH.StableNerve.Transitions
open import DHH.StableNerve.SequenceColimit

private variable ℓ ℓ' : Level

module Stable {ℓ : Level} (G : Graph ℓ) = Colimit (Stage G) (stageTransition G)

-- The actual SET-valued cubical colimit of CK's alternating sequence.
-- Kan fillers and comparison with stable integer-grid functions are
-- separate theorems: neither property is an assumed field here.
N∞ : Graph ℓ → CubicalSet ℓ
N∞ G = Stable.colimitCubical G

includeStage : (G : Graph ℓ) (k : ℕ) → CubicalNatural (Nₘ (suc k) G) (N∞ G)
includeStage G = Stable.include G

includeStage-step : (G : Graph ℓ) (k : ℕ)
  → stageTransition G k ⋆n includeStage G (suc k) ≡ includeStage G k
includeStage-step G = Stable.include-step G

module _ {G : Graph ℓ} {H : Graph ℓ'} (f : Hom G H) where
  mapCocone : Stable.Cocone G (N∞ H)
  Stable.family mapCocone k = Nₘ-map (suc k) f ⋆n includeStage H k
  Stable.compatible mapCocone k n c =
    cong (λ d → Stable.point H n (suc k , d)) (stageTransition-cells-natural f k n c)
    ∙ sym (SQ.eq/ {R = Stable.Step H n} _ _ (Stable.step {G = H} {n = n} {k = k} (mapCells (Nₘ-map (suc k) f) n c)))

  N∞-map : CubicalNatural (N∞ G) (N∞ H)
  N∞-map = Stable.factor G mapCocone

  N∞-map-on-stage : (k : ℕ)
    → includeStage G k ⋆n N∞-map ≡ Nₘ-map (suc k) f ⋆n includeStage H k
  N∞-map-on-stage = Stable.factor-on-stage G mapCocone

N∞-map-id : (G : Graph ℓ) → N∞-map (idHom G) ≡ cubicalId (N∞ G)
N∞-map-id G = cubicalNaturalExt λ n → SQ.elimProp (λ c → SQ.squash/ _ _)
  (λ { (k , c) → cong (λ d → Stable.point G n (k , d)) (leftIdentity c) })

N∞-map-compose : {G H K : Graph ℓ} (f : Hom G H) (g : Hom H K)
  → N∞-map (g ∘g f) ≡ N∞-map f ⋆n N∞-map g
N∞-map-compose {K = K} f g = cubicalNaturalExt λ n → SQ.elimProp (λ c → SQ.squash/ _ _)
  (λ { (k , c) → cong (λ d → Stable.point K n (k , d)) (homExt (λ _ → refl)) })

N∞-functor : (ℓ : Level) → Functor (GraphCategory ℓ) (CubicalSetCategory ℓ)
Functor.F-ob (N∞-functor ℓ) = N∞
Functor.F-hom (N∞-functor ℓ) = N∞-map
Functor.F-id (N∞-functor ℓ) {x = G} = N∞-map-id G
Functor.F-seq (N∞-functor ℓ) = N∞-map-compose
