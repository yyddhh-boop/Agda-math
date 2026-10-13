{-# OPTIONS --cubical --safe #-}
module DHH.Localization.RigidLevelwiseLaws where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base
open import DHH.Cubes using (Position; weakenPosition; there;
  CoordinatePair; lower; upper; lowerWide; upperWide)
open import DHH.Localization.Ordinary using (canonical)
open import DHH.Localization.OrdinaryEvaluation
open import DHH.Localization.RelativeFree
open import DHH.Localization.OrdinaryFunctor
open import DHH.Localization.ExtensionComparison
open import DHH.Localization.LevelwiseCore
import DHH.Localization.ResolutionOperators as Res

open RelativeFunctor
open Functor
private variable ℓ : Level
module _ {C : Category ℓ ℓ} (R : Marking C) where

  facesHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
    (u : Category.Hom[_,_] (LocalizedPower R (suc (suc n))) x y)
    → F-hom (localCollapse R (upper p))
        (F-hom (localCollapse R (lowerWide p)) u)
      ≡ F-hom (localCollapse R (lower p))
        (F-hom (localCollapse R (upperWide p)) u)
  facesHom {n = n} p u = compareExtensions K inv Eleft Eright u
    where
    A = Res.Power C (suc (suc n))
    D = Res.Power C n
    P = PowerMarking R (suc (suc n))
    T = PowerMarking R n
    F = collapseRelative R (lowerWide p)
    G = collapseRelative R (upper p)
    F′ = collapseRelative R (upperWide p)
    G′ = collapseRelative R (lower p)
    K = localBase (RelativeCompose F G)
    inv = localInverts (RelativeCompose F G)
    L = funcComp (LocalFunctor G) (LocalFunctor F)
    M = funcComp (LocalFunctor G′) (LocalFunctor F′)
    Eleft : Extension K inv
    Extension.hom Eleft = F-hom L
    Extension.hom-id Eleft = F-id L
    Extension.hom-compose Eleft = F-seq L
    Extension.agrees Eleft f =
      cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
      ∙ LocalFunctor-original G (F-hom (functor F) f)
    Eright : Extension K inv
    Extension.hom Eright = F-hom M
    Extension.hom-id Eright = F-id M
    Extension.hom-compose Eright = F-seq M
    Extension.agrees Eright f =
      cong (F-hom (LocalFunctor G′)) (LocalFunctor-original F′ f)
      ∙ LocalFunctor-original G′ (F-hom (functor F′) f)
      ∙ cong (F-hom (canonical D (Marking.marked T))) (sym (Res.facesHom C p f))

  degensHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
    (u : Category.Hom[_,_] (LocalizedPower R (suc n)) x y)
    → F-hom (localDuplicate R (lowerWide p))
        (F-hom (localDuplicate R (upper p)) u)
      ≡ F-hom (localDuplicate R (upperWide p))
        (F-hom (localDuplicate R (lower p)) u)
  degensHom {n = n} p u = compareExtensions K inv Eleft Eright u
    where
    A = Res.Power C (suc n)
    D = Res.Power C (suc (suc (suc n)))
    P = PowerMarking R (suc n)
    T = PowerMarking R (suc (suc (suc n)))
    F = duplicateRelative R (upper p)
    G = duplicateRelative R (lowerWide p)
    F′ = duplicateRelative R (lower p)
    G′ = duplicateRelative R (upperWide p)
    K = localBase (RelativeCompose F G)
    inv = localInverts (RelativeCompose F G)
    L = funcComp (LocalFunctor G) (LocalFunctor F)
    M = funcComp (LocalFunctor G′) (LocalFunctor F′)
    Eleft : Extension K inv
    Extension.hom Eleft = F-hom L
    Extension.hom-id Eleft = F-id L
    Extension.hom-compose Eleft = F-seq L
    Extension.agrees Eleft f =
      cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
      ∙ LocalFunctor-original G (F-hom (functor F) f)
    Eright : Extension K inv
    Extension.hom Eright = F-hom M
    Extension.hom-id Eright = F-id M
    Extension.hom-compose Eright = F-seq M
    Extension.agrees Eright f =
      cong (F-hom (LocalFunctor G′)) (LocalFunctor-original F′ f)
      ∙ LocalFunctor-original G′ (F-hom (functor F′) f)
      ∙ cong (F-hom (canonical D (Marking.marked T))) (sym (Res.degensHom C p f))

  beforeHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
    (u : Category.Hom[_,_] (LocalizedPower R (suc (suc n))) x y)
    → F-hom (localCollapse R (weakenPosition (lowerWide p)))
        (F-hom (localDuplicate R (upperWide p)) u)
      ≡ F-hom (localDuplicate R (upper p))
        (F-hom (localCollapse R (lowerWide p)) u)
  beforeHom {n = n} p u = compareExtensions K inv Eleft Eright u
    where
    A = Res.Power C (suc (suc n))
    D = Res.Power C (suc (suc n))
    P = PowerMarking R (suc (suc n))
    T = PowerMarking R (suc (suc n))
    F = duplicateRelative R (upperWide p)
    G = collapseRelative R (weakenPosition (lowerWide p))
    F′ = collapseRelative R (lowerWide p)
    G′ = duplicateRelative R (upper p)
    K = localBase (RelativeCompose F G)
    inv = localInverts (RelativeCompose F G)
    L = funcComp (LocalFunctor G) (LocalFunctor F)
    M = funcComp (LocalFunctor G′) (LocalFunctor F′)
    Eleft : Extension K inv
    Extension.hom Eleft = F-hom L
    Extension.hom-id Eleft = F-id L
    Extension.hom-compose Eleft = F-seq L
    Extension.agrees Eleft f =
      cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
      ∙ LocalFunctor-original G (F-hom (functor F) f)
    Eright : Extension K inv
    Extension.hom Eright = F-hom M
    Extension.hom-id Eright = F-id M
    Extension.hom-compose Eright = F-seq M
    Extension.agrees Eright f =
      cong (F-hom (LocalFunctor G′)) (LocalFunctor-original F′ f)
      ∙ LocalFunctor-original G′ (F-hom (functor F′) f)
      ∙ cong (F-hom (canonical D (Marking.marked T))) (sym (Res.beforeHom C p f))

  afterHom : {n : ℕ} (p : CoordinatePair n) {x y : Category.ob C}
    (u : Category.Hom[_,_] (LocalizedPower R (suc (suc n))) x y)
    → F-hom (localCollapse R (there (upperWide p)))
        (F-hom (localDuplicate R (lowerWide p)) u)
      ≡ F-hom (localDuplicate R (lower p))
        (F-hom (localCollapse R (upperWide p)) u)
  afterHom {n = n} p u = compareExtensions K inv Eleft Eright u
    where
    A = Res.Power C (suc (suc n))
    D = Res.Power C (suc (suc n))
    P = PowerMarking R (suc (suc n))
    T = PowerMarking R (suc (suc n))
    F = duplicateRelative R (lowerWide p)
    G = collapseRelative R (there (upperWide p))
    F′ = collapseRelative R (upperWide p)
    G′ = duplicateRelative R (lower p)
    K = localBase (RelativeCompose F G)
    inv = localInverts (RelativeCompose F G)
    L = funcComp (LocalFunctor G) (LocalFunctor F)
    M = funcComp (LocalFunctor G′) (LocalFunctor F′)
    Eleft : Extension K inv
    Extension.hom Eleft = F-hom L
    Extension.hom-id Eleft = F-id L
    Extension.hom-compose Eleft = F-seq L
    Extension.agrees Eleft f =
      cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
      ∙ LocalFunctor-original G (F-hom (functor F) f)
    Eright : Extension K inv
    Extension.hom Eright = F-hom M
    Extension.hom-id Eright = F-id M
    Extension.hom-compose Eright = F-seq M
    Extension.agrees Eright f =
      cong (F-hom (LocalFunctor G′)) (LocalFunctor-original F′ f)
      ∙ LocalFunctor-original G′ (F-hom (functor F′) f)
      ∙ cong (F-hom (canonical D (Marking.marked T))) (sym (Res.afterHom C p f))

  sameHom : {n : ℕ} (j : Position (suc n)) {x y : Category.ob C}
    (u : Category.Hom[_,_] (LocalizedPower R (suc n)) x y)
    → F-hom (localCollapse R (weakenPosition j))
        (F-hom (localDuplicate R j) u) ≡ u
  sameHom {n = n} j u = compareExtensions K inv Eleft Eright u
    where
    A = Res.Power C (suc n)
    D = Res.Power C (suc n)
    P = PowerMarking R (suc n)
    T = PowerMarking R (suc n)
    F = duplicateRelative R j
    G = collapseRelative R (weakenPosition j)
    K = localBase (RelativeCompose F G)
    inv = localInverts (RelativeCompose F G)
    L = funcComp (LocalFunctor G) (LocalFunctor F)
    M : Functor (Local P) (Local T)
    M = Id
    Eleft : Extension K inv
    Extension.hom Eleft = F-hom L
    Extension.hom-id Eleft = F-id L
    Extension.hom-compose Eleft = F-seq L
    Extension.agrees Eleft f =
      cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
      ∙ LocalFunctor-original G (F-hom (functor F) f)
    Eright : Extension K inv
    Extension.hom Eright = F-hom M
    Extension.hom-id Eright = F-id M
    Extension.hom-compose Eright = F-seq M
    Extension.agrees Eright f =
      cong (F-hom (canonical D (Marking.marked T))) (sym (Res.sameHom C j f))

  nextHom : {n : ℕ} (j : Position (suc n)) {x y : Category.ob C}
    (u : Category.Hom[_,_] (LocalizedPower R (suc n)) x y)
    → F-hom (localCollapse R (there j))
        (F-hom (localDuplicate R j) u) ≡ u
  nextHom {n = n} j u = compareExtensions K inv Eleft Eright u
    where
    A = Res.Power C (suc n)
    D = Res.Power C (suc n)
    P = PowerMarking R (suc n)
    T = PowerMarking R (suc n)
    F = duplicateRelative R j
    G = collapseRelative R (there j)
    K = localBase (RelativeCompose F G)
    inv = localInverts (RelativeCompose F G)
    L = funcComp (LocalFunctor G) (LocalFunctor F)
    M : Functor (Local P) (Local T)
    M = Id
    Eleft : Extension K inv
    Extension.hom Eleft = F-hom L
    Extension.hom-id Eleft = F-id L
    Extension.hom-compose Eleft = F-seq L
    Extension.agrees Eleft f =
      cong (F-hom (LocalFunctor G)) (LocalFunctor-original F f)
      ∙ LocalFunctor-original G (F-hom (functor F) f)
    Eright : Extension K inv
    Extension.hom Eright = F-hom M
    Extension.hom-id Eright = F-id M
    Extension.hom-compose Eright = F-seq M
    Extension.agrees Eright f =
      cong (F-hom (canonical D (Marking.marked T))) (sym (Res.nextHom C j f))
