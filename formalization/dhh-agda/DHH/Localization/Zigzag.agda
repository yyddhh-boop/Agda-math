{-# OPTIONS --cubical --safe #-}

module DHH.Localization.Zigzag where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base using (Category; _[_,_])

private
  variable ℓo ℓh ℓw : Level

-- W is a class of ACTUAL arrows.  A backward step must carry evidence
-- that its underlying arrow belongs to W.  No fraction calculus is
-- assumed, and arbitrary finite lengths are allowed.
data Zigzag (C : Category ℓo ℓh)
            (W : {x y : Category.ob C} → C [ x , y ] → Type ℓw)
            : Category.ob C → Category.ob C
            → Type (ℓ-max ℓo (ℓ-max ℓh ℓw)) where
  done : {x : Category.ob C} → Zigzag C W x x
  forward : {x y z : Category.ob C}
          → C [ x , y ] → Zigzag C W y z → Zigzag C W x z
  backward : {x y z : Category.ob C} (f : C [ y , x ])
           → W f → Zigzag C W y z → Zigzag C W x z

module _ {C : Category ℓo ℓh}
         {W : {x y : Category.ob C} → C [ x , y ] → Type ℓw} where

  append : {x y z : Category.ob C}
         → Zigzag C W x y → Zigzag C W y z → Zigzag C W x z
  append done v = v
  append (forward f u) v = forward f (append u v)
  append (backward f w u) v = backward f w (append u v)

  append-unit : {x y : Category.ob C} (u : Zigzag C W x y)
              → append u done ≡ u
  append-unit done = refl
  append-unit (forward f u) = cong (forward f) (append-unit u)
  append-unit (backward f w u) = cong (backward f w) (append-unit u)

  append-assoc : {x y z t : Category.ob C}
               → (u : Zigzag C W x y) (v : Zigzag C W y z)
                 (w : Zigzag C W z t)
               → append (append u v) w ≡ append u (append v w)
  append-assoc done v w = refl
  append-assoc (forward f u) v w =
    cong (forward f) (append-assoc u v w)
  append-assoc (backward f p u) v w =
    cong (backward f p) (append-assoc u v w)

  oneForward : {x y : Category.ob C} → C [ x , y ] → Zigzag C W x y
  oneForward f = forward f done

  oneBackward : {x y : Category.ob C} (f : C [ y , x ])
              → W f → Zigzag C W x y
  oneBackward f w = backward f w done
