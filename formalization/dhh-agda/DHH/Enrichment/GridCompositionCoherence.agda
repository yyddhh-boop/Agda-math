{-# OPTIONS --cubical --safe #-}
module DHH.Enrichment.GridCompositionCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import DHH.Graph
open import DHH.CubeCategory
open import DHH.CubicalNerve
open import DHH.Cubical.TensorCategory
open import DHH.Cubical.TensorCoherence
import DHH.Cubical.TensorCategory.Coordinates as C
open import DHH.StableNerve.Grid
open import DHH.StableNerve.Nerve
open import DHH.Enrichment.GraphHom
open import DHH.Enrichment.GridComposition
open import DHH.Enrichment.GridCompositionNaturality

private variable ℓG ℓH ℓK ℓL ℓT : Level

abstract
  -- The extensionality witnesses use the actual split/append algorithm.
  -- They do not enumerate vertices and apply to arbitrary target graphs.
  gridAppendExt : (r p q : ℕ) {T : Graph ℓT}
    {f g : Hom (Grid r (p + q)) T}
    → ((x : Vertex (Grid r p)) (y : Vertex (Grid r q))
        → onVertices f (appendGridPoint r p q x y)
          ≡ onVertices g (appendGridPoint r p q x y))
    → f ≡ g
  gridAppendExt r p q {f = f} {g = g} e = homExt λ z →
    sym (cong (onVertices f) (append-split-grid-point r p q z))
    ∙ e (fst (splitGridPoint r p q z)) (snd (splitGridPoint r p q z))
    ∙ cong (onVertices g) (append-split-grid-point r p q z)

  gridLeftTripleExt : (r p q s : ℕ) {T : Graph ℓT}
    {f g : Hom (Grid r ((p + q) + s)) T}
    → ((x : Vertex (Grid r p)) (y : Vertex (Grid r q)) (z : Vertex (Grid r s))
        → onVertices f (appendGridPoint r (p + q) s (appendGridPoint r p q x y) z)
          ≡ onVertices g (appendGridPoint r (p + q) s (appendGridPoint r p q x y) z))
    → f ≡ g
  gridLeftTripleExt r p q s {f = f} {g = g} e = gridAppendExt r (p + q) s λ xy z →
    sym (cong (λ t → onVertices f (appendGridPoint r (p + q) s t z))
      (append-split-grid-point r p q xy))
    ∙ e (fst (splitGridPoint r p q xy)) (snd (splitGridPoint r p q xy)) z
    ∙ cong (λ t → onVertices g (appendGridPoint r (p + q) s t z))
      (append-split-grid-point r p q xy)

  -- Threshold separation lifts the genuine Boolean cube associator to
  -- every finite chain, including all dimensions and all interval sizes.
  gridAction-associator-on-append : (r p q s : ℕ)
    (x : Vertex (Grid r p)) (y : Vertex (Grid r q)) (z : Vertex (Grid r s))
    → onVertices (gridAction r (cubeAssociator p q s))
        (appendGridPoint r (p + q) s (appendGridPoint r p q x y) z)
      ≡ appendGridPoint r p (q + s) x (appendGridPoint r q s y z)
  gridAction-associator-on-append r p q s x y z =
    thresholdGrid-ext (p + (q + s)) _ _ λ t →
      gridAction-threshold r (cubeAssociator p q s) t
        (appendGridPoint r (p + q) s (appendGridPoint r p q x y) z)
      ∙ cong (onVertices (underlying (cubeAssociator p q s)))
        (threshold-append-grid t (p + q) s (appendGridPoint r p q x y) z
        ∙ cong (λ a → C.appendPoint (p + q) s a (thresholdGrid t s z))
          (threshold-append-grid t p q x y))
      ∙ cubeAssociator-on-append p q s
        (thresholdGrid t p x) (thresholdGrid t q y) (thresholdGrid t s z)
      ∙ sym (threshold-append-grid t p (q + s) x (appendGridPoint r q s y z)
        ∙ cong (C.appendPoint p (q + s) (thresholdGrid t p x))
          (threshold-append-grid t q s y z))

  gridAction-right-unit-on-append : (r p : ℕ)
    (x : Vertex (Grid r p)) (u : Vertex (Grid r zero))
    → onVertices (gridAction r (cubeRightUnit p))
        (appendGridPoint r p zero x u) ≡ x
  gridAction-right-unit-on-append r p x u = thresholdGrid-ext p _ _ λ t →
    gridAction-threshold r (cubeRightUnit p) t (appendGridPoint r p zero x u)
    ∙ cong (onVertices (underlying (cubeRightUnit p)))
      (threshold-append-grid t p zero x u)
    ∙ cubeRightUnit-on-append p (thresholdGrid t p x) (thresholdGrid t zero u)

  gridAction-right-collapse-on-append : (r p q : ℕ) (v : CubicalMap q zero)
    (x : Vertex (Grid r p)) (y : Vertex (Grid r q))
    → onVertices (gridAction r ((cubeId p ⊗c v) ⋆c cubeRightUnit p))
        (appendGridPoint r p q x y) ≡ x
  gridAction-right-collapse-on-append r p q v x y =
    cong (λ h → onVertices h (appendGridPoint r p q x y))
      (gridAction-compose r (cubeId p ⊗c v) (cubeRightUnit p))
    ∙ cong (onVertices (gridAction r (cubeRightUnit p)))
      (gridAction-tensor-on-append r (cubeId p) v x y)
    ∙ gridAction-right-unit-on-append r p
      (onVertices (gridAction r (cubeId p)) x) (onVertices (gridAction r v) y)
    ∙ cong (λ h → onVertices h x) (gridAction-id r p)

  composeGrid-left-unit : (r p q : ℕ)
    {G : Graph ℓG} {H : Graph ℓH} (v : CubicalMap p zero)
    (b : Cell (Nₘ r (HomGraph G H)) q)
    → composeGridCells r {p = p} {q = q}
        (constantHom (HomGraph H H) (idHom H)) b
      ≡ reindex (Nₘ r (HomGraph G H)) (v ⊗c cubeId q) b
  composeGrid-left-unit r p q {G} {H} v b = gridAppendExt r p q λ x y →
    composeGrid-on-append r {p = p} {q = q}
      (constantHom (HomGraph H H) (idHom H)) b x y
    ∙ leftIdentity (onVertices b y)
    ∙ sym (cong (onVertices b)
        (gridAction-tensor-on-append r v (cubeId q) x y
        ∙ cong (λ h → onVertices h y) (gridAction-id r q)))

  composeGrid-right-unit : (r p q : ℕ)
    {G : Graph ℓG} {H : Graph ℓH} (v : CubicalMap q zero)
    (a : Cell (Nₘ r (HomGraph G H)) p)
    → composeGridCells r {p = p} {q = q}
        a (constantHom (HomGraph G G) (idHom G))
      ≡ reindex (Nₘ r (HomGraph G H))
        ((cubeId p ⊗c v) ⋆c cubeRightUnit p) a
  composeGrid-right-unit r p q {G} {H} v a = gridAppendExt r p q λ x y →
    composeGrid-on-append r {p = p} {q = q}
      a (constantHom (HomGraph G G) (idHom G)) x y
    ∙ rightIdentity (onVertices a x)
    ∙ sym (cong (onVertices a) (gridAction-right-collapse-on-append r p q v x y))

  composeGrid-associativity : (r p q s : ℕ)
    {G : Graph ℓG} {H : Graph ℓH} {K : Graph ℓK} {L : Graph ℓL}
    (a : Cell (Nₘ r (HomGraph K L)) p)
    (b : Cell (Nₘ r (HomGraph H K)) q)
    (c : Cell (Nₘ r (HomGraph G H)) s)
    → composeGridCells r {p = p + q} {q = s}
        (composeGridCells r {p = p} {q = q} a b) c
      ≡ reindex (Nₘ r (HomGraph G L)) (cubeAssociator p q s)
        (composeGridCells r {p = p} {q = q + s}
          a (composeGridCells r {p = q} {q = s} b c))
  composeGrid-associativity r p q s a b c = gridLeftTripleExt r p q s λ x y z →
    composeGrid-on-append r {p = p + q} {q = s}
      (composeGridCells r {p = p} {q = q} a b) c (appendGridPoint r p q x y) z
    ∙ cong (_∘g onVertices c z) (composeGrid-on-append r {p = p} {q = q} a b x y)
    ∙ homExt (λ _ → refl)
    ∙ sym
      (cong (onVertices (composeGridCells r {p = p} {q = q + s}
          a (composeGridCells r {p = q} {q = s} b c)))
        (gridAction-associator-on-append r p q s x y z)
      ∙ composeGrid-on-append r {p = p} {q = q + s}
          a (composeGridCells r {p = q} {q = s} b c) x (appendGridPoint r q s y z)
      ∙ cong (onVertices a x ∘g_) (composeGrid-on-append r {p = q} {q = s} b c y z))
