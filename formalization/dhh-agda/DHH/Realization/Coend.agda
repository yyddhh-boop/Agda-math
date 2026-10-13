{-# OPTIONS --cubical --safe #-}

module DHH.Realization.Coend where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category; _^op)
open import Cubical.Categories.Functor.Base using (Functor)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.NaturalTransformation.Base using (NatTrans)
import Cubical.HITs.SetQuotients as SQ
open import DHH.Topology.Base

private
  variable ℓ : Level

-- The geometric disks form a COVARIANT diagram.  An instance with the
-- standard topological cubes/simplexes must be supplied separately.
-- This parameter is visible: it is not an axiom asserting existence.
record DiskDiagram (C : Category ℓ-zero ℓ-zero) (ℓ : Level)
                   : Type (ℓ-suc ℓ) where
  field
    disk : Category.ob C → Top ℓ
    diskMap : {a b : Category.ob C} → Category.Hom[_,_] C a b
            → Continuous (disk a) (disk b)
    disk-id : {a : Category.ob C}
            → diskMap (Category.id C {x = a}) ≡ identityContinuous (disk a)
    disk-compose : {a b c : Category.ob C}
                   (f : Category.Hom[_,_] C a b) (g : Category.Hom[_,_] C b c)
                 → diskMap (Category._⋆_ C f g)
                   ≡ composeContinuous (diskMap g) (diskMap f)
open DiskDiagram public

pullbackDisks : {C C' : Category ℓ-zero ℓ-zero}
              → Functor C C' → DiskDiagram C' ℓ → DiskDiagram C ℓ
disk (pullbackDisks F D) a = disk D (Functor.F-ob F a)
diskMap (pullbackDisks F D) u = diskMap D (Functor.F-hom F u)
disk-id (pullbackDisks F D) = cong (diskMap D) (Functor.F-id F) ∙ disk-id D
disk-compose (pullbackDisks F D) f g =
  cong (diskMap D) (Functor.F-seq F f g)
  ∙ disk-compose D (Functor.F-hom F f) (Functor.F-hom F g)

SetPresheaf : Category ℓ-zero ℓ-zero → (ℓ : Level) → Type (ℓ-suc ℓ)
SetPresheaf C ℓ = Functor (C ^op) (SET ℓ)

module Realization {C : Category ℓ-zero ℓ-zero}
                   (D : DiskDiagram C ℓ) (K : SetPresheaf C ℓ) where
  open Category C using (ob; Hom[_,_])

  Pieces : Type ℓ
  Pieces = Σ[ a ∈ ob ] (fst (Functor.F-ob K a) × Carrier (disk D a))

  -- Index objects need not be a set in an arbitrary library Category.
  -- Realization below therefore takes that proof explicitly; the cube
  -- and simplex categories both have Nat objects and provide it.

  data Glue : Pieces → Pieces → Type ℓ where
    glue : {a b : ob} (u : Hom[ a , b ])
           (c : fst (Functor.F-ob K b)) (t : Carrier (disk D a))
         → Glue (a , Functor.F-hom K u c , t)
                (b , c , carrierMap (diskMap D u) t)

  -- 构造视角：全维 cell 的集合商加最终拓扑，靠消去原则定义映射。
  -- 通用实现未给出点的规范形或等号判定；实际可执行计算需另说明输入表示。
  Points : Type ℓ
  Points = Pieces SQ./ Glue

  point : (a : ob) → fst (Functor.F-ob K a) → Carrier (disk D a) → Points
  point a c t = SQ.[ a , c , t ]

  face-identification : {a b : ob} (u : Hom[ a , b ])
                        (c : fst (Functor.F-ob K b)) (t : Carrier (disk D a))
                      → point a (Functor.F-hom K u c) t
                        ≡ point b c (carrierMap (diskMap D u) t)
  face-identification u c t = SQ.eq/ _ _ (glue u c t)

  -- The coproduct topology remembers the topology on EVERY disk.  It is
  -- essential: Points alone is a set, not the homotopy type |K|.
  coproductTopology : Topology Pieces
  Topology.Open coproductTopology U =
    ((a : ob) (c : fst (Functor.F-ob K a))
      → fst (Topology.Open (topology (disk D a)) (λ t → U (a , c , t)))) ,
    isPropΠ2 (λ a c → snd (Topology.Open (topology (disk D a)) _))
  Topology.whole-open coproductTopology a c =
    Topology.whole-open (topology (disk D a))
  Topology.empty-open coproductTopology a c =
    Topology.empty-open (topology (disk D a))
  Topology.meet-open coproductTopology U V p q a c =
    Topology.meet-open (topology (disk D a))
      (λ t → U (a , c , t)) (λ t → V (a , c , t)) (p a c) (q a c)
  Topology.union-open coproductTopology J U p a c =
    Topology.union-open (topology (disk D a)) J
      (λ j t → U j (a , c , t)) (λ j → p j a c)

  module _ (objects-isSet : isSet ob) where
    coproductTop : Top ℓ
    Carrier coproductTop = Pieces
    carrier-isSet coproductTop = isSetΣ objects-isSet
      (λ a → isSet× (snd (Functor.F-ob K a)) (carrier-isSet (disk D a)))
    topology coproductTop = coproductTopology

    realize : Top ℓ
    realize = finalTop coproductTop (Points , SQ.squash/) SQ.[_]

    quotient : Continuous coproductTop realize
    quotient = quotientMap coproductTop (Points , SQ.squash/) SQ.[_]

    includeDisk : (a : ob) (c : fst (Functor.F-ob K a))
                → Continuous (disk D a) realize
    carrierMap (includeDisk a c) = point a c
    continuous (includeDisk a c) U p = p a c

    -- Every compatible family of continuous disk maps factors uniquely.
    -- This is the topological coend universal property, proved here.
    record CompatibleDisks (Y : Top ℓ) : Type (ℓ-suc ℓ) where
      field
        family : (a : ob) (c : fst (Functor.F-ob K a))
               → Continuous (disk D a) Y
        compatible : {a b : ob} (u : Hom[ a , b ])
                     (c : fst (Functor.F-ob K b)) (t : Carrier (disk D a))
                   → carrierMap (family a (Functor.F-hom K u c)) t
                     ≡ carrierMap (family b c) (carrierMap (diskMap D u) t)
    open CompatibleDisks public

    -- 已给每个 disk 上的连续映射与全部粘接相容性，便可下降到实现。
    -- 这一泛性质是后续组合构造的接口，不需枚举实现中的所有点。
    factor : {Y : Top ℓ} → CompatibleDisks Y → Continuous realize Y
    carrierMap (factor {Y} F) = SQ.rec (carrier-isSet Y)
      (λ { (a , c , t) → carrierMap (family F a c) t })
      (λ { _ _ (glue u c t) → compatible F u c t })
    continuous (factor F) U p a c = continuous (family F a c) U p

    factor-on-disk : {Y : Top ℓ} (F : CompatibleDisks Y)
                     (a : ob) (c : fst (Functor.F-ob K a))
                   → composeContinuous (factor F) (includeDisk a c) ≡ family F a c
    factor-on-disk F a c = continuousExt (λ _ → refl)

    factor-unique : {Y : Top ℓ} (F : CompatibleDisks Y)
                    (h : Continuous realize Y)
                  → ((a : ob) (c : fst (Functor.F-ob K a))
                    → composeContinuous h (includeDisk a c) ≡ family F a c)
                  → h ≡ factor F
    factor-unique {Y} F h p = continuousExt
      (SQ.elimProp (λ _ → carrier-isSet Y _ _)
        (λ { (a , c , t) → cong (λ f → carrierMap f t) (p a c) }))

-- Mapping a presheaf into another presheaf induces an ACTUAL continuous
-- map between the quotient spaces.  No localization or equivalence is
-- assumed by this definition.
module RealizationMap {C : Category ℓ-zero ℓ-zero}
                      (objects-isSet : isSet (Category.ob C))
                      (D : DiskDiagram C ℓ)
                      {K L : SetPresheaf C ℓ} (η : NatTrans K L) where
  module R = Realization D K
  module S = Realization D L

  onPieces : R.Pieces → S.Points
  onPieces (a , c , t) = S.point a (NatTrans.N-ob η a c) t

  respectsGlue : (p q : R.Pieces) → R.Glue p q → onPieces p ≡ onPieces q
  respectsGlue _ _ (R.glue {a} {b} u c t) =
    cong (λ k → S.point a k t) (funExt⁻ (NatTrans.N-hom η u) c)
    ∙ S.face-identification u (NatTrans.N-ob η b c) t

  realizeFunction : R.Points → S.Points
  realizeFunction = SQ.rec SQ.squash/ onPieces respectsGlue

  realizeMap : Continuous (R.realize objects-isSet) (S.realize objects-isSet)
  carrierMap realizeMap = realizeFunction
  continuous realizeMap U p a c = p a (NatTrans.N-ob η a c)

  realizeMap-on-cell : (a : Category.ob C) (c : fst (Functor.F-ob K a))
                      (t : Carrier (disk D a))
                    → realizeFunction (R.point a c t)
                      ≡ S.point a (NatTrans.N-ob η a c) t
  realizeMap-on-cell a c t = refl
