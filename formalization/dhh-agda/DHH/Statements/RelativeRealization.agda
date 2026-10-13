{-# OPTIONS --cubical --safe #-}

module DHH.Statements.RelativeRealization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base using (Category)
open import Cubical.Categories.Functor.Base using (Functor)
open import DHH.Graph
open import DHH.GraphSets
open import DHH.Topology.Base
open import DHH.Topology.Category
open import DHH.Topology.WeakEquivalence
open import DHH.Realization.Graph
open import DHH.Localization.RelativeFree using (Marking; RelativeFunctor)

-- Raise HOM UNIVERSES only.  Vertices, edges and graph maps are unchanged.
-- This aligns Gra and Top with the homogeneous-universe free resolution.
RaisedGraphCategory : (ℓ : Level) → Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Category.ob (RaisedGraphCategory ℓ) = Graph ℓ
Category.Hom[_,_] (RaisedGraphCategory ℓ) G H = Lift (Hom G H)
Category.id (RaisedGraphCategory ℓ) = lift (idHom _)
Category._⋆_ (RaisedGraphCategory ℓ) f g = lift (lower g ∘g lower f)
Category.⋆IdL (RaisedGraphCategory ℓ) f = cong lift (rightIdentity (lower f))
Category.⋆IdR (RaisedGraphCategory ℓ) f = cong lift (leftIdentity (lower f))
Category.⋆Assoc (RaisedGraphCategory ℓ) f g h =
  cong lift (sym (associativity (lower h) (lower g) (lower f)))
Category.isSetHom (RaisedGraphCategory ℓ) = isOfHLevelLift 2 isSetGraphHom

module RelativeRealization {ℓ : Level} (E : CubeGeometry ℓ) where
  module R = GraphRealization E
  module HG = HomotopyGroups E

  topMarking : Marking (TopCategory ℓ)
  Marking.marked topMarking = HG.WeakHomotopyEquivalence
  Marking.marked-isProp topMarking = HG.weak-isProp
  Marking.marked-id topMarking = HG.weak-id _
  Marking.marked-compose topMarking = HG.weak-compose

  graphMarking : Marking (RaisedGraphCategory ℓ)
  Marking.marked graphMarking f = R.W (lower f)
  Marking.marked-isProp graphMarking f = HG.weak-isProp (R.NG-map (lower f))
  Marking.marked-id graphMarking {G} =
    subst HG.WeakHomotopyEquivalence (sym (R.NG-map-id G)) (HG.weak-id (R.NG G))
  Marking.marked-compose graphMarking f g p q =
    subst HG.WeakHomotopyEquivalence (sym (R.NG-map-compose (lower f) (lower g)))
      (HG.weak-compose (R.NG-map (lower f)) (R.NG-map (lower g)) p q)

  raisedNG : Functor (RaisedGraphCategory ℓ) (TopCategory ℓ)
  Functor.F-ob raisedNG = R.NG
  Functor.F-hom raisedNG f = R.NG-map (lower f)
  Functor.F-id raisedNG = R.NG-map-id _
  Functor.F-seq raisedNG f g = R.NG-map-compose (lower f) (lower g)

  NG-relative : RelativeFunctor graphMarking topMarking
  RelativeFunctor.functor NG-relative = raisedNG
  RelativeFunctor.preservesMarked NG-relative f p = p
