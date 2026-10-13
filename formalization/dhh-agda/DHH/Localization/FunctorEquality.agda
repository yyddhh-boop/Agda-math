{-# OPTIONS --cubical --safe #-}
module DHH.Localization.FunctorEquality where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open Category
open Functor
private variable ℓc ℓh ℓd ℓk : Level

-- Seal the structure-field coherence construction before specializing it
-- to large quotient categories. Morphismwise equations remain the API
-- used by the mapping simplicial sets.
abstract
  functorEquality : {C : Category ℓc ℓh} {D : Category ℓd ℓk}
    {F G : Functor C D}
    (p : (x : ob C) → F-ob F x ≡ F-ob G x)
    (q : {x y : ob C} (u : C [ x , y ])
       → PathP (λ i → D [ p x i , p y i ]) (F-hom F u) (F-hom G u))
    → F ≡ G
  functorEquality = Functor≡
