{-# OPTIONS --cubical --safe #-}

module DHH.PresheafInterop where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (fst)
open import Cubical.Categories.Category.Base using (_^op)
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.NaturalTransformation.Base using (NatTrans)
open import DHH.CubeCategory
open import DHH.CubicalNerve

private
  variable ℓ ℓ' : Level

-- The project's explicit API is interoperable with the library's
-- ordinary presheaf API; no different cube category is substituted.
asPresheaf : CubicalSet ℓ → Functor (CubeCategory ^op) (SET ℓ)
Functor.F-ob (asPresheaf A) = cells A
Functor.F-hom (asPresheaf A) = reindex A
Functor.F-id (asPresheaf A) = funExt (reindex-id A)
Functor.F-seq (asPresheaf A) f g = funExt (reindex-compose A g f)

fromPresheaf : Functor (CubeCategory ^op) (SET ℓ) → CubicalSet ℓ
cells (fromPresheaf F) = Functor.F-ob F
reindex (fromPresheaf F) = Functor.F-hom F
reindex-id (fromPresheaf F) c = funExt⁻ (Functor.F-id F) c
reindex-compose (fromPresheaf F) f g c = funExt⁻ (Functor.F-seq F g f) c

asNaturalTransformation : {A B : CubicalSet ℓ}
                         → CubicalNatural A B → NatTrans (asPresheaf A) (asPresheaf B)
NatTrans.N-ob (asNaturalTransformation η) = mapCells η
NatTrans.N-hom (asNaturalTransformation η) f = funExt (natural η f)
