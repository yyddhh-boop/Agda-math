{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.GraphCoendAdjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.Categories.Adjoint as Adj
import DHH.Cubical.GraphCoend as GC
open GC using (Γₘ-functor; Nₘ-functor; toNerve-postcompose; fromNerve-precompose)

-- 同 universe 时给库中的实际 natural-bijection 伴随记录。
-- 核心 GraphCoend 的 Hom Iso 还允许来源、目标处于不同 universe。
graphNerveAdjunction : (m : ℕ) (ℓ : Level)
  → Adj.NaturalBijection._⊣_ (Γₘ-functor m ℓ) (Nₘ-functor m ℓ)
Adj.NaturalBijection._⊣_.adjIso (graphNerveAdjunction m ℓ) {c = A} {d = G} =
  GC.GraphCoend.graphNerveIso m A G
Adj.NaturalBijection._⊣_.adjNatInD (graphNerveAdjunction m ℓ) {c = A} f k =
  toNerve-postcompose m A f k
Adj.NaturalBijection._⊣_.adjNatInC (graphNerveAdjunction m ℓ) {d = G} g h =
  fromNerve-precompose m G g h
