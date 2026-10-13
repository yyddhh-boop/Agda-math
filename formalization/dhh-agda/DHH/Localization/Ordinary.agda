{-# OPTIONS --cubical --safe #-}

module DHH.Localization.Ordinary where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Localization.Zigzag
import Cubical.HITs.SetQuotients as SQ

open Category
open isIso

private
  variable ℓo ℓh ℓw : Level

-- The usual generating relations for an ORDINARY localization.
-- The quotient is a set and therefore deliberately forgets higher
-- homotopies.  It must never be identified with Gra[W^-1]_infinity.
data Relation (C : Category ℓo ℓh)
              (W : {x y : ob C} → C [ x , y ] → Type ℓw)
              : {x y : ob C} → Zigzag C W x y → Zigzag C W x y
              → Type (ℓ-max ℓo (ℓ-max ℓh ℓw)) where
  unit : {x y : ob C} (z : Zigzag C W x y)
       → Relation C W (forward (id C) z) z
  compose : {x y z t : ob C} (f : C [ x , y ]) (g : C [ y , z ])
            (u : Zigzag C W z t)
          → Relation C W (forward f (forward g u))
                         (forward (_⋆_ C f g) u)
  cancelForward : {x y z : ob C} (f : C [ x , y ]) (w : W f)
                  (u : Zigzag C W x z)
                → Relation C W (forward f (backward f w u)) u
  cancelBackward : {x y z : ob C} (f : C [ x , y ]) (w : W f)
                   (u : Zigzag C W y z)
                 → Relation C W (backward f w (forward f u)) u
  appendLeft : {x y z : ob C} {u v : Zigzag C W x y}
             → Relation C W u v → (r : Zigzag C W y z)
             → Relation C W (append u r) (append v r)
  appendRight : {x y z : ob C} (r : Zigzag C W x y)
                {u v : Zigzag C W y z}
              → Relation C W u v
              → Relation C W (append r u) (append r v)

module _ (C : Category ℓo ℓh)
         (W : {x y : ob C} → C [ x , y ] → Type ℓw) where

  LocalHom : (x y : ob C) → Type (ℓ-max ℓo (ℓ-max ℓh ℓw))
  LocalHom x y = Zigzag C W x y SQ./ Relation C W

  classZigzag : {x y : ob C} → Zigzag C W x y → LocalHom x y
  classZigzag z = SQ.[ z ]

  relationPath : {x y : ob C} {u v : Zigzag C W x y}
               → Relation C W u v → classZigzag u ≡ classZigzag v
  relationPath {u = u} {v = v} r = SQ.eq/ u v r

  localCompose : {x y z : ob C} → LocalHom x y → LocalHom y z
                → LocalHom x z
  localCompose = SQ.rec2 SQ.squash/
    (λ u v → classZigzag (append u v))
    (λ u u' v r → relationPath (appendLeft r v))
    (λ u v v' r → relationPath (appendRight u r))

  localUnitLeft : {x y : ob C} (f : LocalHom x y)
                → localCompose (classZigzag done) f ≡ f
  localUnitLeft = SQ.elimProp (λ _ → SQ.squash/ _ _) (λ _ → refl)

  localUnitRight : {x y : ob C} (f : LocalHom x y)
                 → localCompose f (classZigzag done) ≡ f
  localUnitRight = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ u → cong classZigzag (append-unit u))

  localAssoc : {x y z t : ob C}
             → (u : LocalHom x y) (v : LocalHom y z) (w : LocalHom z t)
             → localCompose (localCompose u v) w
               ≡ localCompose u (localCompose v w)
  localAssoc = SQ.elimProp3 (λ _ _ _ → SQ.squash/ _ _)
    (λ u v w → cong classZigzag (append-assoc u v w))

  OrdinaryLocalization : Category ℓo (ℓ-max ℓo (ℓ-max ℓh ℓw))
  ob OrdinaryLocalization = ob C
  Hom[_,_] OrdinaryLocalization = LocalHom
  id OrdinaryLocalization = classZigzag done
  _⋆_ OrdinaryLocalization = localCompose
  ⋆IdL OrdinaryLocalization = localUnitLeft
  ⋆IdR OrdinaryLocalization = localUnitRight
  ⋆Assoc OrdinaryLocalization = localAssoc
  isSetHom OrdinaryLocalization = SQ.squash/

  canonical : Functor C OrdinaryLocalization
  Functor.F-ob canonical x = x
  Functor.F-hom canonical f = classZigzag (oneForward f)
  Functor.F-id canonical = relationPath (unit done)
  Functor.F-seq canonical f g = sym (relationPath (compose f g done))

  markedIsIso : {x y : ob C} (f : C [ x , y ]) → W f
               → isIso OrdinaryLocalization (Functor.F-hom canonical f)
  inv (markedIsIso f w) = classZigzag (oneBackward f w)
  sec (markedIsIso f w) = relationPath (cancelBackward f w done)
  ret (markedIsIso f w) = relationPath (cancelForward f w done)
