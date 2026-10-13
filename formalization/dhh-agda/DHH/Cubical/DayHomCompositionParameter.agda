{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionParameter where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _+_)
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCoherence
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTensorFunctor
open import DHH.Cubical.DayAssociator
open import DHH.Cubical.DayClosed
open import DHH.Cubical.DayHomEvaluation
open import DHH.Cubical.DayHomCompositionCore
open import DHH.Cubical.DayHomCompositionMaps using (homCompositionEvaluation-β)

private variable ℓ : Level

open import DHH.Cubical.DayHomCompositionParameterEvaluationCore public
open import DHH.Cubical.DayHomCompositionParameterPairing public

-- This is the full concrete evaluation after parameter substitution.
-- Each reduction crosses an exported equation or a checked generator β.
abstract
  homParameterEvaluation-β : (X Y A B C : CubicalSet ℓ)
    (F : CubicalNatural (DayTensor X B) C)
    (G : CubicalNatural (DayTensor Y A) B) (p q r : ℕ)
    (x : Cell X p) (y : Cell Y q) (a : Cell A r)
    → mapCells {A = DayTensor (DayTensor X Y) A} {B = C}
        (homParameterEvaluation X Y A B C F G) ((p + q) + r)
        (leftTripleCell X Y A p q r x y a)
      ≡ reindex C (cubeAssociator p q r)
          (mapCells {A = DayTensor X B} {B = C} F (p + (q + r))
            (dayPair {A = X} {B = B} p (q + r) x
              (mapCells {A = DayTensor Y A} {B = B} G (q + r)
                (dayPair {A = Y} {B = A} q r y a))))
  homParameterEvaluation-β {ℓ} X Y A B C F G p q r x y a =
    let
      H : CubicalSet ℓ
      H = DayHom B C
      K : CubicalSet ℓ
      K = DayHom A B
      P : CubicalSet ℓ
      P = DayTensor X Y
      Q : CubicalSet ℓ
      Q = DayTensor H K
      L : CubicalSet ℓ
      L = DayTensor P A
      M : CubicalSet ℓ
      M = DayTensor Q A
      parameter : CubicalNatural P Q
      parameter = homParameter X Y A B C F G
      outerParameter : CubicalNatural L M
      outerParameter = dayMap {A = P} {A' = Q} {B = A} {B' = A} parameter (cubicalId A)
      compositionEvaluation : CubicalNatural M C
      compositionEvaluation = homCompositionEvaluation A B C
      concreteRoute : CubicalNatural L C
      concreteRoute = _⋆n_ {A = L} {B = M} {C = C} outerParameter compositionEvaluation
      t : Cell L ((p + q) + r)
      t = leftTripleCell X Y A p q r x y a
      xy : Cell P (p + q)
      xy = dayPair {A = X} {B = Y} p q x y
      hx : Cell H p
      hx = mapCells {A = X} {B = H} (curryDay {C = X} {A = B} {B = C} F) p x
      ky : Cell K q
      ky = mapCells {A = Y} {B = K} (curryDay {C = Y} {A = A} {B = B} G) q y
      hk : Cell Q (p + q)
      hk = dayPair {A = H} {B = K} p q hx ky
      s : Cell M ((p + q) + r)
      s = leftTripleCell H K A p q r hx ky a
      u : CubicalMap ((p + q) + r) (p + (q + r))
      u = cubeAssociator p q r
      v : Cell B (q + r)
      v = applyHom A B q r ky a
      w : Cell B (q + r)
      w = mapCells {A = DayTensor Y A} {B = B} G (q + r)
        (dayPair {A = Y} {B = A} q r y a)
      applyHx : Cell B (q + r) → Cell C (p + (q + r))
      applyHx = applyHom B C p (q + r) hx
      value : Cell C (p + (q + r))
      value = mapCells {A = DayTensor X B} {B = C} F (p + (q + r))
        (dayPair {A = X} {B = B} p (q + r) x w)

      routeCell : mapCells {A = L} {B = C} (homParameterEvaluation X Y A B C F G) ((p + q) + r) t
        ≡ mapCells {A = L} {B = C} concreteRoute ((p + q) + r) t
      routeCell = cong (λ (h : CubicalNatural L C) → mapCells {A = L} {B = C} h ((p + q) + r) t)
        (homParameterEvaluation-route X Y A B C F G)
      mapOuter : mapCells {A = L} {B = M} outerParameter ((p + q) + r) t
        ≡ dayPair {A = Q} {B = A} (p + q) r (mapCells {A = P} {B = Q} parameter (p + q) xy) a
      mapOuter = dayMap-β {A = P} {A' = Q} {B = A} {B' = A}
        parameter (cubicalId A) (p + q) r xy a
      mapInner : mapCells {A = P} {B = Q} parameter (p + q) xy ≡ hk
      mapInner = homParameter-β X Y A B C F G p q x y
      pairedInner : dayPair {A = Q} {B = A} (p + q) r
          (mapCells {A = P} {B = Q} parameter (p + q) xy) a ≡ s
      pairedInner = cong (λ (z : Cell Q (p + q)) → dayPair {A = Q} {B = A} (p + q) r z a) mapInner
      b1 : mapCells {A = L} {B = C} concreteRoute ((p + q) + r) t
        ≡ mapCells {A = M} {B = C} compositionEvaluation ((p + q) + r) s
      b1 = cong (mapCells {A = M} {B = C} compositionEvaluation ((p + q) + r))
        (mapOuter ∙ pairedInner)
      b2 : mapCells {A = M} {B = C} compositionEvaluation ((p + q) + r) s
        ≡ reindex C u (applyHx v)
      b2 = homCompositionEvaluation-β A B C p q r hx ky a
      evalG : v ≡ w
      evalG = applyHom-curry-β Y A B G q r y a
      evalF : applyHx w ≡ value
      evalF = applyHom-curry-β X B C F p (q + r) x w
      evaluatedG : applyHx v ≡ applyHx w
      evaluatedG = cong applyHx evalG
      b3 : reindex C u (applyHx v) ≡ reindex C u value
      b3 = cong (reindex C u) (evaluatedG ∙ evalF)
    in routeCell ∙ b1 ∙ b2 ∙ b3
