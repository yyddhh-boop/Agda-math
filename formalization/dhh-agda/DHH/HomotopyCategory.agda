{-# OPTIONS --cubical --safe #-}

module DHH.HomotopyCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Categories.Category.Base using (Category; CatIso; catiso)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Graph
open import DHH.Homotopy

private
  variable
    ℓ : Level
    G H K L : Graph ℓ

-- The ordinary homotopy category: a morphism remembers only the
-- finite-chain homotopy class of a graph map.  This deliberately uses
-- a SET quotient, since morphisms of an ordinary category form a set.
-- It is not the higher localization Gra[W^{-1}]_∞ occurring in DHH.
HoHom : (G H : Graph ℓ) → Type ℓ
HoHom G H = Hom G H SQ./ Chain {G = G} {H = H}

classHom : Hom G H → HoHom G H
classHom f = SQ.[ f ]

chain-equality : {f g : Hom G H} → Chain f g
               → classHom f ≡ classHom g
chain-equality {f = f} {g = g} c = SQ.eq/ f g c

-- Composition descends because finite homotopies can be whiskered
-- both before and after another graph map.
hoCompose : {G H K : Graph ℓ} → HoHom G H → HoHom H K → HoHom G K
hoCompose {G = G} {H = H} {K = K} = SQ.rec2 SQ.squash/
  (λ f g → classHom (g ∘g f))
  (λ f f' g c → chain-equality
    (chain-whisker-post {G = G} {H = H} {K = K}
      {f = f} {g = f'} g c))
  (λ f g g' c → chain-equality
    (chain-whisker-pre {G = H} {H = K} {K = G}
      {f = g} {g = g'} f c))

hoIdentityLeft : (f : HoHom G H)
               → hoCompose (classHom (idHom G)) f ≡ f
hoIdentityLeft = SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ f → cong classHom (rightIdentity f))

hoIdentityRight : (f : HoHom G H)
                → hoCompose f (classHom (idHom H)) ≡ f
hoIdentityRight = SQ.elimProp (λ _ → SQ.squash/ _ _)
  (λ f → cong classHom (leftIdentity f))

hoAssociativity : (f : HoHom G H) (g : HoHom H K) (h : HoHom K L)
                 → hoCompose (hoCompose f g) h ≡ hoCompose f (hoCompose g h)
hoAssociativity = SQ.elimProp3 (λ _ _ _ → SQ.squash/ _ _)
  (λ f g h → cong classHom (sym (associativity h g f)))

HoGraph : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.ob (HoGraph ℓ) = Graph ℓ
Category.Hom[_,_] (HoGraph ℓ) = HoHom
Category.id (HoGraph ℓ) {x = G} = classHom (idHom G)
Category._⋆_ (HoGraph ℓ) = hoCompose
Category.⋆IdL (HoGraph ℓ) = hoIdentityLeft
Category.⋆IdR (HoGraph ℓ) = hoIdentityRight
Category.⋆Assoc (HoGraph ℓ) = hoAssociativity
Category.isSetHom (HoGraph ℓ) = SQ.squash/

-- A concrete graph homotopy equivalence supplies an isomorphism in
-- this ordinary category.  No assertion about weak equivalences or
-- higher mapping spaces is included in this result.
record GraphHomotopyEquivalence (G H : Graph ℓ) : Type ℓ where
  field
    forward : Hom G H
    backward : Hom H G
    retract : Chain (backward ∘g forward) (idHom G)
    section : Chain (forward ∘g backward) (idHom H)

graphEquivalenceToIso : {G H : Graph ℓ} → GraphHomotopyEquivalence G H
                       → CatIso (HoGraph ℓ) G H
graphEquivalenceToIso e = catiso
  (classHom (GraphHomotopyEquivalence.forward e))
  (classHom (GraphHomotopyEquivalence.backward e))
  (chain-equality (GraphHomotopyEquivalence.section e))
  (chain-equality (GraphHomotopyEquivalence.retract e))
