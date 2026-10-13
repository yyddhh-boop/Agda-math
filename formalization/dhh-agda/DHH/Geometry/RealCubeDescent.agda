{-# OPTIONS --cubical --safe #-}

module DHH.Geometry.RealCubeDescent where

open import Cubical.Foundations.Prelude hiding (Cube; lower)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Rationals.Base using (ℚ; fromNatℚ)
import Cubical.Data.Rationals.Order as O
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using (Dec; ¬_; yes; no)
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.Graph using (Vertex; onVertices)
open import DHH.Cubes using (Q; Position; here; there; insert; delete; merge; meetBool; joinBool)
open import DHH.CubeCategory
open import DHH.Topology.Base
open import DHH.Geometry.DedekindReals
open import DHH.Geometry.RealTopology
open import DHH.Geometry.RealCubes

-- A constructive, deliberately overlapping approximation to a real
-- threshold.  Locatedness chooses a Boolean across a rational GAP;
-- it never decides p<x for an arbitrary real x.
GapBit : (p q : ℚ) → Bool → ClosedUnitInterval → Type₀
GapBit p q false x = fst (upperCut (fst x) q)
GapBit p q true x = fst (lowerCut (fst x) p)

GapCube : (p q : ℚ) (n : ℕ) → Vertex (Q n) → Carrier (RealCube n) → Type₀
GapCube p q zero b x = Unit
GapCube p q (suc n) (b , bs) (x , xs) = GapBit p q b x × GapCube p q n bs xs

-- 构造视角：按有限坐标数递归，但结果在命题截断内：只提供近似存在性。
-- 因此不能从本接口一般地抽出一个具体 Bool 向量或实数比较判定器。
chooseGapCube : (p q : ℚ) → p O.< q → (n : ℕ) (x : Carrier (RealCube n))
  → ∥ Σ[ b ∈ Vertex (Q n) ] GapCube p q n b x ∥₁
chooseGapCube p q pq zero x = ∣ tt , tt ∣₁
chooseGapCube p q pq (suc n) (x , xs) = PT.rec2 squash₁
  (λ { (inl lx) (bs , hs) → ∣ (true , bs) , lx , hs ∣₁
     ; (inr ux) (bs , hs) → ∣ (false , bs) , ux , hs ∣₁ })
  (located (cutLaws (fst x)) p q pq) (chooseGapCube p q pq n xs)

boolCoordinate : {n : ℕ} → Position n → Vertex (Q n) → Bool
boolCoordinate here x = fst x
boolCoordinate (there p) x = boolCoordinate p (snd x)

gap-coordinate : (p q : ℚ) {n : ℕ} (i : Position n)
  (b : Vertex (Q n)) (x : Carrier (RealCube n)) → GapCube p q n b x
  → GapBit p q (boolCoordinate i b) (carrierMap (CubePowers.coordinate i) x)
gap-coordinate p q here b x h = fst h
gap-coordinate p q (there i) b x h = gap-coordinate p q i (snd b) (snd x) (snd h)

module GapPreservation (p q : ℚ) (q-positive : 0 O.< q) (p-below-one : p O.< 1) where
  endpoint-gap : (b : Bool) → GapBit p q b (endpoint b)
  endpoint-gap false = q-positive
  endpoint-gap true = p-below-one

  insert-gap : {n : ℕ} (i : Position (suc n)) (v : Bool)
    (b : Vertex (Q n)) (x : Carrier (RealCube n)) → GapCube p q n b x
    → GapCube p q (suc n) (insert i v b)
        (carrierMap (CubePowers.insertMap i (endpoint v)) x)
  insert-gap here v b x h = endpoint-gap v , h
  insert-gap {n = suc n} (there i) v (b , bs) (x , xs) (h , hs) =
    h , insert-gap i v bs xs hs

  delete-gap : {n : ℕ} (i : Position (suc n))
    (b : Vertex (Q (suc n))) (x : Carrier (RealCube (suc n))) → GapCube p q (suc n) b x
    → GapCube p q n (delete i b) (carrierMap (CubePowers.deleteMap i) x)
  delete-gap here (b , bs) (x , xs) (h , hs) = hs
  delete-gap {n = suc n} (there i) (b , bs) (x , xs) (h , hs) =
    h , delete-gap i bs xs hs

  min-gap : (a b : Bool) (x y : ClosedUnitInterval)
    → GapBit p q a x → GapBit p q b y → GapBit p q (meetBool a b) (intervalMin x y)
  min-gap false false x y hx hy = ∣ inl hx ∣₁
  min-gap false true x y hx hy = ∣ inl hx ∣₁
  min-gap true false x y hx hy = ∣ inr hy ∣₁
  min-gap true true x y hx hy = hx , hy

  max-gap : (a b : Bool) (x y : ClosedUnitInterval)
    → GapBit p q a x → GapBit p q b y → GapBit p q (joinBool a b) (intervalMax x y)
  max-gap false false x y hx hy = hx , hy
  max-gap false true x y hx hy = ∣ inr hy ∣₁
  max-gap true false x y hx hy = ∣ inl hx ∣₁
  max-gap true true x y hx hy = ∣ inl hx ∣₁

  merge-gap : {n : ℕ} (i : Position (suc n))
    (op : Bool → Bool → Bool)
    (opR : Continuous IntervalProduct.productTop closedUnitInterval)
    (pres : (a b : Bool) (x y : ClosedUnitInterval)
      → GapBit p q a x → GapBit p q b y → GapBit p q (op a b) (carrierMap opR (x , y)))
    (b : Vertex (Q (suc (suc n)))) (x : Carrier (RealCube (suc (suc n))))
    → GapCube p q (suc (suc n)) b x
    → GapCube p q (suc n) (merge i op b) (carrierMap (CubePowers.mergeMap i opR) x)
  merge-gap here op opR pres (a , b , bs) (x , y , xs) (ha , hb , hs) = pres a b x y ha hb , hs
  merge-gap {n = suc n} (there i) op opR pres (a , bs) (x , xs) (h , hs) =
    h , merge-gap i op opR pres bs xs hs

  -- 证明视角：对生成词结构归纳；composeW 组合两份保持性证明。
  -- 这是可组合的不变量证明，结论适用于任意词和维数。
  word-gap : {m n : ℕ} (w : CubeWord m n) (b : Vertex (Q m)) (x : Carrier (RealCube m))
    → GapCube p q m b x
    → GapCube p q n (onVertices (evaluate w) b) (carrierMap (realCubeWord w) x)
  word-gap identityW b x h = h
  word-gap (faceW i v) b x h = insert-gap i v b x h
  word-gap (deleteW i) b x h = delete-gap i b x h
  word-gap (minW i) b x h = merge-gap i meetBool intervalMinContinuous min-gap b x h
  word-gap (maxW i) b x h = merge-gap i joinBool intervalMaxContinuous max-gap b x h
  word-gap (composeW f g) b x h =
    word-gap g (onVertices (evaluate f) b) (carrierMap (realCubeWord f) x) (word-gap f b x h)

gap-transfer : (p q : ℚ) (b : Bool) (x y : ClosedUnitInterval)
  → GapBit p q b x → GapBit p q b y
  → fst (lowerCut (fst x) q) → fst (lowerCut (fst y) p)
gap-transfer p q false x y ux uy lx =
  Empty.rec (O.isIrrefl< q (separated (cutLaws (fst x)) q q lx ux))
gap-transfer p q true x y lx ly lqx = ly

-- Every rational lower bound of one real-valued word is a lower bound
-- of a Boolean-equal word.  Negative bounds follow from [0,1]; all
-- other bounds use a rounded gap and a finite locatedness choice.
word-lower-inclusion : {m n : ℕ} (f g : CubeWord m n)
  → ((b : Vertex (Q m)) → onVertices (evaluate f) b ≡ onVertices (evaluate g) b)
  → (x : Carrier (RealCube m)) (i : Position n) (p : ℚ)
  → fst (lowerCut (fst (carrierMap (CubePowers.coordinate i) (carrierMap (realCubeWord f) x))) p)
  → fst (lowerCut (fst (carrierMap (CubePowers.coordinate i) (carrierMap (realCubeWord g) x))) p)
word-lower-inclusion {m} {n} f g eq x i p lp = decide (O.<Dec p 0)
  where
  yf yg : ClosedUnitInterval
  yf = carrierMap (CubePowers.coordinate i) (carrierMap (realCubeWord f) x)
  yg = carrierMap (CubePowers.coordinate i) (carrierMap (realCubeWord g) x)

  rounded : (¬ (p O.< 0)) → Σ[ q ∈ ℚ ] (p O.< q) × fst (lowerCut (fst yf) q)
    → fst (lowerCut (fst yg) p)
  rounded p-nonnegative (q , pq , lq) = PT.rec (snd (lowerCut (fst yg) p)) transfer
    (chooseGapCube p q pq m x)
    where
    q-positive : 0 O.< q
    q-positive = O.isTrans≤< 0 p q (O.≮→≥ p 0 p-nonnegative) pq
    p-below-one : p O.< 1
    p-below-one = O.isTrans< p q 1 pq (fst (snd (snd yf)) q lq)
    module Preserve = GapPreservation p q q-positive p-below-one

    transfer : Σ[ b ∈ Vertex (Q m) ] GapCube p q m b x → fst (lowerCut (fst yg) p)
    transfer (b , h) = gap-transfer p q (boolCoordinate i (onVertices (evaluate f) b)) yf yg
      (gap-coordinate p q i _ _ (Preserve.word-gap f b x h))
      (gap-coordinate p q i _ _
        (subst (λ c → GapCube p q n c (carrierMap (realCubeWord g) x))
          (sym (eq b)) (Preserve.word-gap g b x h))) lq

  decide : Dec (p O.< 0) → fst (lowerCut (fst yg) p)
  decide (yes p-negative) = fst (fst (snd yg)) p p-negative
  decide (no p-nonnegative) = PT.rec (snd (lowerCut (fst yg) p)) (rounded p-nonnegative)
    (lower-rounded (cutLaws (fst yf)) p lp)

realCubeWord-ext : {m n : ℕ} (f g : CubeWord m n)
  → evaluate f ≡ evaluate g → realCubeWord f ≡ realCubeWord g
realCubeWord-ext f g eq = continuousExt λ x → CubePowers.powerPointExt λ i →
  intervalExt (realLowerExt
    (word-lower-inclusion f g (λ b → cong (λ h → onVertices h b) eq) x i)
    (word-lower-inclusion g f (λ b → cong (λ h → onVertices h b) (sym eq)) x i))
