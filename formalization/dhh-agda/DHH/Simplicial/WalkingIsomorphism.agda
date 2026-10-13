{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.WalkingIsomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool; false; true; not; isSetBool; notnot)
open import Cubical.Data.Sigma
open import DHH.Simplicial.Ordinal
open import DHH.Simplicial.Sets
open import DHH.Simplicial.Products

private variable ℓ ℓ' : Level

-- 两对象且每对对象之间有唯一箭头的群胚之 nerve。
-- n-cell 是 n+1 个端点的列表；相邻箭头由唯一性自动确定。
-- 因此重索引只需预合成，不枚举或选择箭头。
WalkingIso : SimplicialSet ℓ-zero
simplexes WalkingIso n = (Fin (suc n) → Bool) , isSetΠ (λ _ → isSetBool)
reindexS WalkingIso f c i = c (mapIndex f i)
reindexS-id WalkingIso c = refl
reindexS-compose WalkingIso f g c = refl

isoEndpoint : (b : Bool) → SimplicialNatural TerminalS WalkingIso
mapS (isoEndpoint b) n c i = b
naturalS (isoEndpoint b) f c = refl

reverseIso : SimplicialNatural WalkingIso WalkingIso
mapS reverseIso n c i = not (c i)
naturalS reverseIso f c = refl

reverseIso-twice : reverseIso ⋆s reverseIso ≡ simplicialId WalkingIso
reverseIso-twice = simplicialNaturalExt (λ n c → funExt (λ i → notnot (c i)))

atIsoEndpoint : (A : SimplicialSet ℓ) (b : Bool)
  → SimplicialNatural A (SProduct A WalkingIso)
atIsoEndpoint A b = pairS (simplicialId A) (terminalSMap A ⋆s isoEndpoint b)

record IsoHomotopy {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
                   (f g : SimplicialNatural A B) : Type (ℓ-max ℓ ℓ') where
  field
    homotopy : SimplicialNatural (SProduct A WalkingIso) B
    atFalse : atIsoEndpoint A false ⋆s homotopy ≡ f
    atTrue : atIsoEndpoint A true ⋆s homotopy ≡ g
open IsoHomotopy public

isoHomotopy-refl : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  (f : SimplicialNatural A B) → IsoHomotopy f f
homotopy (isoHomotopy-refl {A = A} f) = firstS {A = A} {B = WalkingIso} ⋆s f
atFalse (isoHomotopy-refl f) = simplicialNaturalExt (λ n c → refl)
atTrue (isoHomotopy-refl f) = simplicialNaturalExt (λ n c → refl)

isoHomotopy-sym : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  {f g : SimplicialNatural A B} → IsoHomotopy f g → IsoHomotopy g f
homotopy (isoHomotopy-sym {A = A} h) = productSMap (simplicialId A) reverseIso ⋆s homotopy h
atFalse (isoHomotopy-sym {A = A} {B = B} h) =
  simplicialNaturalExt {A = A} {B = B} (λ n c → refl) ∙ atTrue h
atTrue (isoHomotopy-sym {A = A} {B = B} h) =
  simplicialNaturalExt {A = A} {B = B} (λ n c → refl) ∙ atFalse h

-- 此处构造的是群胚区间同伦数据；没有把“有这样的参数对象”
-- 直接当成局部化泛性质或原文比较已证。
