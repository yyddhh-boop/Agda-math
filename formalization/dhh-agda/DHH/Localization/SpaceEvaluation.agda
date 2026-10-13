{-# OPTIONS --cubical --safe #-}

module DHH.Localization.SpaceEvaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Categories.Category.Base using (Category; _[_,_])
open import DHH.Localization.Zigzag
open import DHH.Localization.Ordinary using (Relation; unit; compose;
  cancelForward; cancelBackward; appendLeft; appendRight)

private
  variable ℓo ℓh ℓw ℓs : Level

-- Unlike an ordinary target category, these mapping TYPES need not
-- be sets.  Consequently this interpretation retains higher paths.
-- It is an interface to be instantiated by a genuine construction
-- such as the geometric realization functor, not a definition of it.
record SpaceInterpretation (C : Category ℓo ℓh)
       (W : {x y : Category.ob C} → C [ x , y ] → Type ℓw)
       (ℓs : Level) : Type (ℓ-max (ℓ-suc ℓs) (ℓ-max ℓo (ℓ-max ℓh ℓw))) where
  field
    space : Category.ob C → Type ℓs
    map : {x y : Category.ob C} → C [ x , y ] → space x → space y
    map-id : {x : Category.ob C} → map (Category.id C) ≡ (λ (a : space x) → a)
    map-compose : {x y z : Category.ob C} (f : C [ x , y ]) (g : C [ y , z ])
                → map (Category._⋆_ C f g) ≡ (λ a → map g (map f a))
    map-inverts : {x y : Category.ob C} (f : C [ x , y ])
                → W f → isEquiv (map f)

module _ {C : Category ℓo ℓh}
         {W : {x y : Category.ob C} → C [ x , y ] → Type ℓw}
         (S : SpaceInterpretation C W ℓs) where

  open SpaceInterpretation S

  markedEquivalence : {x y : Category.ob C} (f : C [ x , y ])
                    → W f → space x ≃ space y
  markedEquivalence f w = map f , map-inverts f w

  evaluateSpace : {x y : Category.ob C} → Zigzag C W x y
                → space x → space y
  evaluateSpace done a = a
  evaluateSpace (forward f u) a = evaluateSpace u (map f a)
  evaluateSpace (backward f w u) a =
    evaluateSpace u (invEq (markedEquivalence f w) a)

  evaluateSpace-append : {x y z : Category.ob C}
                       → (u : Zigzag C W x y) (v : Zigzag C W y z)
                       → evaluateSpace (append u v)
                         ≡ (λ a → evaluateSpace v (evaluateSpace u a))
  evaluateSpace-append done v = refl
  evaluateSpace-append (forward f u) v i a =
    evaluateSpace-append u v i (map f a)
  evaluateSpace-append (backward f w u) v i a =
    evaluateSpace-append u v i (invEq (markedEquivalence f w) a)

  -- Every relation has a genuine homotopy in the target mapping type.
  -- This does NOT give a map from the SET quotient LocalHom into this
  -- mapping type: the requisite 2- and all higher coherences are not
  -- supplied here, and arbitrary functions need not form a set.
  evaluateSpace-relation : {x y : Category.ob C}
                           {u v : Zigzag C W x y}
                         → Relation C W u v
                         → evaluateSpace u ≡ evaluateSpace v
  evaluateSpace-relation (unit u) i a = evaluateSpace u (map-id i a)
  evaluateSpace-relation (compose f g u) i a =
    evaluateSpace u (map-compose f g (~ i) a)
  evaluateSpace-relation (cancelForward f w u) i a =
    evaluateSpace u (retEq (markedEquivalence f w) a i)
  evaluateSpace-relation (cancelBackward f w u) i a =
    evaluateSpace u (secEq (markedEquivalence f w) a i)
  evaluateSpace-relation (appendLeft {u = u} {v = v} r z) =
    evaluateSpace-append u z
    ∙ cong (λ k a → evaluateSpace z (k a)) (evaluateSpace-relation r)
    ∙ sym (evaluateSpace-append v z)
  evaluateSpace-relation (appendRight z {u = u} {v = v} r) =
    evaluateSpace-append z u
    ∙ cong (λ k a → k (evaluateSpace z a)) (evaluateSpace-relation r)
    ∙ sym (evaluateSpace-append z v)
