{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.KanTransport where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import DHH.CubicalNerve
open import DHH.Cubical.Faces
open import DHH.Cubical.Kan
open import DHH.StableNerve.UniversalHornReduction using
  (mapExtension; changeExtensionBoundary)

private variable ℓA ℓB : Level

-- B 是 A 的实际预层 retract：f 后接 g 是 A 上的另一复合，
-- 而这里需要的等式是 g 后接 f = id_B。输入 B 的整个 horn
-- 先后合成 g，在 A 中填充，再把填充 cell 后合成 f。
-- 以下边界等式在全部维数和所有 horn cells 上使用同一个逆式。
module Retraction {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (f : CubicalNatural A B) (g : CubicalNatural B A)
  (rightInverse : g ⋆n f ≡ cubicalId B) where

  roundTripBoundary : {n : ℕ} {missing : Facet n}
    (box : CubicalNatural (OpenBox missing) B)
    → (box ⋆n g) ⋆n f ≡ box
  roundTripBoundary box = cubicalNaturalExt λ m c →
    cong (λ h → mapCells h m (mapCells box m c)) rightInverse

  transportExtension : {n : ℕ} {missing : Facet n}
    (box : CubicalNatural (OpenBox missing) B)
    → OpenBoxExtension A missing (box ⋆n g)
    → OpenBoxExtension B missing box
  transportExtension box e = changeExtensionBoundary (roundTripBoundary box)
    (mapExtension f e)

-- PT.map 的值仍然是填充的截断存在；不从 IsKan 抽取一个
-- ChosenKanFillings，也不为所有 horn 选择代表或填充程序。
kanAlongNaturalRetraction : {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (f : CubicalNatural A B) (g : CubicalNatural B A)
  → g ⋆n f ≡ cubicalId B → IsKan A → IsKan B
kanAlongNaturalRetraction f g rightInverse kan n missing box =
  PT.map (Retraction.transportExtension f g rightInverse box)
    (kan n missing (box ⋆n g))

-- 自然同构的两个方向分别使用相应的逆式。列出两条逆式
-- 使模型比较的应用直接接受完整自然同构，且精确标明方向。
kanAlongNaturalIso : {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (f : CubicalNatural A B) (g : CubicalNatural B A)
  → f ⋆n g ≡ cubicalId A → g ⋆n f ≡ cubicalId B
  → IsKan A → IsKan B
kanAlongNaturalIso f g leftInverse rightInverse =
  kanAlongNaturalRetraction f g rightInverse

kanAlongNaturalIsoBack : {A : CubicalSet ℓA} {B : CubicalSet ℓB}
  (f : CubicalNatural A B) (g : CubicalNatural B A)
  → f ⋆n g ≡ cubicalId A → g ⋆n f ≡ cubicalId B
  → IsKan B → IsKan A
kanAlongNaturalIsoBack f g leftInverse rightInverse =
  kanAlongNaturalRetraction g f leftInverse

-- 宇宙参数分别量化 A 与 B；证明不要求任一预层有限、可枚举、
-- 有可判定相等，或对其 cells 的存在性作非命题截断消去。
