{-# OPTIONS --cubical --safe #-}
module DHH.Simplicial.Products where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Sigma
open import DHH.Simplicial.Sets

private variable ℓ ℓ' ℓ'' ℓ''' : Level

-- 单纯集合的积逐阶定义；与原文立方集合的几何 tensor 不同。
-- 给定两份 cell 就返回 pair，重索引及所有规律逐分量跟随构造。
SProduct : SimplicialSet ℓ → SimplicialSet ℓ' → SimplicialSet (ℓ-max ℓ ℓ')
simplexes (SProduct A B) n = (SCell A n × SCell B n) ,
  isSet× (snd (simplexes A n)) (snd (simplexes B n))
reindexS (SProduct A B) f (a , b) = reindexS A f a , reindexS B f b
reindexS-id (SProduct A B) (a , b) = cong₂ _,_ (reindexS-id A a) (reindexS-id B b)
reindexS-compose (SProduct A B) f g (a , b) =
  cong₂ _,_ (reindexS-compose A f g a) (reindexS-compose B f g b)

firstS : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} → SimplicialNatural (SProduct A B) A
mapS firstS n = fst
naturalS firstS f c = refl

secondS : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} → SimplicialNatural (SProduct A B) B
mapS secondS n = snd
naturalS secondS f c = refl

pairS : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} {C : SimplicialSet ℓ''}
  → SimplicialNatural A B → SimplicialNatural A C → SimplicialNatural A (SProduct B C)
mapS (pairS f g) n a = mapS f n a , mapS g n a
naturalS (pairS f g) u a = cong₂ _,_ (naturalS f u a) (naturalS g u a)

pair-first : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} {C : SimplicialSet ℓ''}
  (f : SimplicialNatural A B) (g : SimplicialNatural A C)
  → pairS f g ⋆s firstS {A = B} {B = C} ≡ f
pair-first {A = A} {B = B} f g = simplicialNaturalExt {A = A} {B = B} (λ n c → refl)

pair-second : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} {C : SimplicialSet ℓ''}
  (f : SimplicialNatural A B) (g : SimplicialNatural A C)
  → pairS f g ⋆s secondS {A = B} {B = C} ≡ g
pair-second {A = A} {C = C} f g = simplicialNaturalExt {A = A} {B = C} (λ n c → refl)

pair-unique : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'} {C : SimplicialSet ℓ''}
  (h : SimplicialNatural A (SProduct B C))
  → pairS (h ⋆s firstS {A = B} {B = C}) (h ⋆s secondS {A = B} {B = C}) ≡ h
pair-unique {A = A} {B = B} {C = C} h =
  simplicialNaturalExt {A = A} {B = SProduct B C} (λ n c → refl)

productSMap : {A : SimplicialSet ℓ} {B : SimplicialSet ℓ'}
  {C : SimplicialSet ℓ''} {D : SimplicialSet ℓ'''}
  → SimplicialNatural A B → SimplicialNatural C D
  → SimplicialNatural (SProduct A C) (SProduct B D)
productSMap {A = A} {B = B} {C = C} {D = D} f g =
  pairS {A = SProduct A C} {B = B} {C = D}
    (firstS {A = A} {B = C} ⋆s f) (secondS {A = A} {B = C} ⋆s g)

TerminalS : SimplicialSet ℓ-zero
simplexes TerminalS n = Unit , isProp→isSet isPropUnit
reindexS TerminalS f c = c
reindexS-id TerminalS c = refl
reindexS-compose TerminalS f g c = refl

terminalSMap : (A : SimplicialSet ℓ) → SimplicialNatural A TerminalS
mapS (terminalSMap A) n c = tt
naturalS (terminalSMap A) f c = refl

terminalS-unique : {A : SimplicialSet ℓ} (f : SimplicialNatural A TerminalS)
  → f ≡ terminalSMap A
terminalS-unique f = simplicialNaturalExt (λ n c → isPropUnit _ _)
