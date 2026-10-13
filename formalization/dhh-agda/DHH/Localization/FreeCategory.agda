{-# OPTIONS --cubical --safe #-}

module DHH.Localization.FreeCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.UnderlyingGraph using (Cat→Graph)
open import Cubical.Data.Graph.Base using (GraphHom; _$g_; _<$g>_)
import Cubical.Categories.Constructions.Free.Category.Base as LibraryFree

open Functor

private
  variable ℓo ℓh ℓdo ℓdh ℓeo ℓeh : Level

-- The free category on ALL arrows of C.  An existing identity arrow
-- becomes a generator, distinct from the new free identity; an existing
-- composite arrow becomes one generator, distinct from a two-letter word.
-- This distinction is what the Dwyer--Kan resolution needs.
-- LibraryFree uses a HIT with category laws and set-valued homs; its
-- universal property is already established in the pinned library.
Free : Category ℓo ℓh → Category ℓo (ℓ-max ℓo ℓh)
Free C = LibraryFree.FreeCategory.FreeCat (Cat→Graph C)

generator : {C : Category ℓo ℓh} {x y : Category.ob C}
          → Category.Hom[_,_] C x y → Category.Hom[_,_] (Free C) x y
generator {C = C} f = LibraryFree.FreeCategory.↑_ {G = Cat→Graph C} f

FreeFunctor : {C : Category ℓo ℓh} {D : Category ℓdo ℓdh}
            → Functor C D → Functor (Free C) (Free D)
FreeFunctor {C = C} {D = D} F =
  LibraryFree.FreeCategory.Semantics.sem (Cat→Graph C) (Free D)
    (record { _$g_ = F-ob F ; _<$g>_ = λ f → generator {C = D} (F-hom F f) })

epsilon : (C : Category ℓo ℓh) → Functor (Free C) C
epsilon C = LibraryFree.ε

delta : (C : Category ℓo ℓh) → Functor (Free C) (Free (Free C))
delta C = LibraryFree.FreeCategory.Semantics.sem (Cat→Graph C) (Free (Free C))
  (record { _$g_ = λ x → x
          ; _<$g>_ = λ f → generator {C = Free C} (generator {C = C} f) })

-- 构造视角：Semantics.sem 是自由对象的消去原则，指定生成元的像即可
-- 延拓到复合表达式，并满足范畴关系。对任意 C，这不是箭头枚举或相等判定。
-- epsilon 将嵌套表达式求值；delta 给生成元再加一层，相关相容性如下证明。
-- Every proof below uses the free-category induction principle:
-- agreement on generators implies agreement on all finite words.
FreeFunctor-identity : (C : Category ℓo ℓh)
                    → FreeFunctor (Id {C = C}) ≡ Id
FreeFunctor-identity C = LibraryFree.FreeCategory.induction (Cat→Graph C)
  (FreeFunctor (Id {C = C})) Id refl

FreeFunctor-composition : {C : Category ℓo ℓh} {D : Category ℓdo ℓdh}
                          {E : Category ℓeo ℓeh}
                        → (F : Functor C D) (G : Functor D E)
                        → FreeFunctor (funcComp G F)
                          ≡ funcComp (FreeFunctor G) (FreeFunctor F)
FreeFunctor-composition {C = C} F G =
  LibraryFree.FreeCategory.induction (Cat→Graph C)
    (FreeFunctor (funcComp G F))
    (funcComp (FreeFunctor G) (FreeFunctor F)) refl

epsilon-natural : {C : Category ℓo ℓh} {D : Category ℓdo ℓdh}
                → (F : Functor C D)
                → funcComp (epsilon D) (FreeFunctor F)
                  ≡ funcComp F (epsilon C)
epsilon-natural {C = C} {D = D} F =
  LibraryFree.FreeCategory.induction (Cat→Graph C)
    (funcComp (epsilon D) (FreeFunctor F))
    (funcComp F (epsilon C)) refl

delta-natural : {C : Category ℓo ℓh} {D : Category ℓdo ℓdh}
              → (F : Functor C D)
              → funcComp (delta D) (FreeFunctor F)
                ≡ funcComp (FreeFunctor (FreeFunctor F)) (delta C)
delta-natural {C = C} {D = D} F =
  LibraryFree.FreeCategory.induction (Cat→Graph C)
    (funcComp (delta D) (FreeFunctor F))
    (funcComp (FreeFunctor (FreeFunctor F)) (delta C)) refl

epsilon-delta : (C : Category ℓo ℓh)
              → funcComp (epsilon (Free C)) (delta C) ≡ Id
epsilon-delta C = LibraryFree.FreeCategory.induction (Cat→Graph C)
  (funcComp (epsilon (Free C)) (delta C)) Id refl

Free-epsilon-delta : (C : Category ℓo ℓh)
                   → funcComp (FreeFunctor (epsilon C)) (delta C) ≡ Id
Free-epsilon-delta C = LibraryFree.FreeCategory.induction (Cat→Graph C)
  (funcComp (FreeFunctor (epsilon C)) (delta C)) Id refl

delta-coassoc : (C : Category ℓo ℓh)
              → funcComp (delta (Free C)) (delta C)
                ≡ funcComp (FreeFunctor (delta C)) (delta C)
delta-coassoc C = LibraryFree.FreeCategory.induction (Cat→Graph C)
  (funcComp (delta (Free C)) (delta C))
  (funcComp (FreeFunctor (delta C)) (delta C)) refl
