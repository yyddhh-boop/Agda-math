{-# OPTIONS --cubical --safe #-}

module DHH.Localization.OrdinaryEvaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Localization.Zigzag
open import DHH.Localization.Ordinary
import Cubical.HITs.SetQuotients as SQ

open Category
open isIso
open Functor

private
  variable ℓo ℓh ℓw ℓdo ℓdh : Level

module _ {C : Category ℓo ℓh}
         {W : {x y : ob C} → C [ x , y ] → Type ℓw}
         {D : Category ℓdo ℓdh}
         (F : Functor C D)
         (inverts : {x y : ob C} (f : C [ x , y ])
                  → W f → isIso D (F-hom F f)) where

  evaluate : {x y : ob C} → Zigzag C W x y
           → D [ F-ob F x , F-ob F y ]
  evaluate done = id D
  evaluate (forward f u) = _⋆_ D (F-hom F f) (evaluate u)
  evaluate (backward f w u) = _⋆_ D (inv (inverts f w)) (evaluate u)

  evaluate-append : {x y z : ob C}
                  → (u : Zigzag C W x y) (v : Zigzag C W y z)
                  → evaluate (append u v) ≡ _⋆_ D (evaluate u) (evaluate v)
  evaluate-append done v = sym (⋆IdL D (evaluate v))
  evaluate-append (forward f u) v =
    cong (_⋆_ D (F-hom F f)) (evaluate-append u v)
    ∙ sym (⋆Assoc D (F-hom F f) (evaluate u) (evaluate v))
  evaluate-append (backward f w u) v =
    cong (_⋆_ D (inv (inverts f w))) (evaluate-append u v)
    ∙ sym (⋆Assoc D (inv (inverts f w)) (evaluate u) (evaluate v))

  evaluate-relation : {x y : ob C} {u v : Zigzag C W x y}
                    → Relation C W u v → evaluate u ≡ evaluate v
  evaluate-relation (unit u) =
    cong (λ a → _⋆_ D a (evaluate u)) (F-id F)
    ∙ ⋆IdL D (evaluate u)
  evaluate-relation (compose f g u) =
    sym (⋆Assoc D (F-hom F f) (F-hom F g) (evaluate u))
    ∙ cong (λ a → _⋆_ D a (evaluate u)) (sym (F-seq F f g))
  evaluate-relation (cancelForward f w u) =
    sym (⋆Assoc D (F-hom F f) (inv (inverts f w)) (evaluate u))
    ∙ cong (λ a → _⋆_ D a (evaluate u)) (ret (inverts f w))
    ∙ ⋆IdL D (evaluate u)
  evaluate-relation (cancelBackward f w u) =
    sym (⋆Assoc D (inv (inverts f w)) (F-hom F f) (evaluate u))
    ∙ cong (λ a → _⋆_ D a (evaluate u)) (sec (inverts f w))
    ∙ ⋆IdL D (evaluate u)
  evaluate-relation (appendLeft {u = u} {v = v} r z) =
    evaluate-append u z
    ∙ cong (λ a → _⋆_ D a (evaluate z)) (evaluate-relation r)
    ∙ sym (evaluate-append v z)
  evaluate-relation (appendRight z {u = u} {v = v} r) =
    evaluate-append z u
    ∙ cong (_⋆_ D (evaluate z)) (evaluate-relation r)
    ∙ sym (evaluate-append z v)

  -- A genuine extension into any ORDINARY category that inverts W.
  -- The target hom-sets justify the set-quotient elimination.
  abstract
    evaluateLocal : {x y : ob C} → LocalHom C W x y
                  → D [ F-ob F x , F-ob F y ]
    evaluateLocal = SQ.rec (isSetHom D) evaluate
      (λ u v → evaluate-relation)

    evaluateLocal-id : {x : ob C}
      → evaluateLocal (classZigzag C W (done {x = x})) ≡ id D
    evaluateLocal-id = refl

    evaluateLocal-compose : {x y z : ob C}
      (u : LocalHom C W x y) (v : LocalHom C W y z)
      → evaluateLocal (localCompose C W u v)
        ≡ _⋆_ D (evaluateLocal u) (evaluateLocal v)
    evaluateLocal-compose = SQ.elimProp2 (λ _ _ → isSetHom D _ _)
      evaluate-append

  extension : Functor (OrdinaryLocalization C W) D
  F-ob extension = F-ob F
  F-hom extension = evaluateLocal
  F-id extension = evaluateLocal-id
  F-seq extension = evaluateLocal-compose

  abstract
    extension-on-arrow : {x y : ob C} (f : C [ x , y ])
                       → F-hom extension (F-hom (canonical C W) f)
                         ≡ F-hom F f
    extension-on-arrow f = ⋆IdR D (F-hom F f)

    extension-on-inverse : {x y : ob C} (f : C [ x , y ]) (w : W f)
                         → evaluateLocal (classZigzag C W (oneBackward f w))
                           ≡ inv (inverts f w)
    extension-on-inverse f w = ⋆IdR D (inv (inverts f w))

  -- We keep the object function fixed to F-ob F.  This is the strict
  -- objectwise form of the ordinary localization universal property.
  -- In particular the extension is UNIQUE on every morphism, not just
  -- one arbitrarily chosen evaluation of words.
  record Extension : Type (ℓ-max ℓo (ℓ-max ℓh (ℓ-max ℓw ℓdh))) where
    field
      hom : {x y : ob C} → LocalHom C W x y
          → D [ F-ob F x , F-ob F y ]
      hom-id : {x : ob C} → hom (classZigzag C W (done {x = x})) ≡ id D
      hom-compose : {x y z : ob C} (u : LocalHom C W x y) (v : LocalHom C W y z)
                  → hom (localCompose C W u v) ≡ _⋆_ D (hom u) (hom v)
      agrees : {x y : ob C} (f : C [ x , y ])
             → hom (F-hom (canonical C W) f) ≡ F-hom F f

  canonicalExtension : Extension
  Extension.hom canonicalExtension = evaluateLocal
  Extension.hom-id canonicalExtension = evaluateLocal-id
  Extension.hom-compose canonicalExtension = F-seq extension
  Extension.agrees canonicalExtension = extension-on-arrow

  module _ (K : Extension) where
    open Extension K

    imageInverse : {x y : ob C} (f : C [ x , y ]) (w : W f)
                 → isIso D (F-hom F f)
    inv (imageInverse f w) = hom (classZigzag C W (oneBackward f w))
    sec (imageInverse f w) =
      cong (_⋆_ D (hom (classZigzag C W (oneBackward f w)))) (sym (agrees f))
      ∙ sym (hom-compose (classZigzag C W (oneBackward f w))
                         (classZigzag C W (oneForward f)))
      ∙ cong hom (relationPath C W (cancelBackward f w done))
      ∙ hom-id
    ret (imageInverse f w) =
      cong (λ a → _⋆_ D a (hom (classZigzag C W (oneBackward f w))))
           (sym (agrees f))
      ∙ sym (hom-compose (classZigzag C W (oneForward f))
                         (classZigzag C W (oneBackward f w)))
      ∙ cong hom (relationPath C W (cancelForward f w done))
      ∙ hom-id

    agreesInverse : {x y : ob C} (f : C [ x , y ]) (w : W f)
                   → hom (classZigzag C W (oneBackward f w))
                     ≡ inv (inverts f w)
    agreesInverse f w = cong inv
      (isPropIsIso (F-hom F f) (imageInverse f w) (inverts f w))

    unique-on-zigzag : {x y : ob C} (u : Zigzag C W x y)
                     → hom (classZigzag C W u) ≡ evaluate u
    unique-on-zigzag done = hom-id
    unique-on-zigzag (forward f u) =
      hom-compose (classZigzag C W (oneForward f)) (classZigzag C W u)
      ∙ cong₂ (_⋆_ D) (agrees f) (unique-on-zigzag u)
    unique-on-zigzag (backward f w u) =
      hom-compose (classZigzag C W (oneBackward f w)) (classZigzag C W u)
      ∙ cong₂ (_⋆_ D) (agreesInverse f w) (unique-on-zigzag u)

    abstract
      unique-on-hom : {x y : ob C} (u : LocalHom C W x y)
                    → hom u ≡ evaluateLocal u
      unique-on-hom = SQ.elimProp (λ _ → isSetHom D _ _) unique-on-zigzag
