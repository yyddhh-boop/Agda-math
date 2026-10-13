{-# OPTIONS --cubical --safe #-}
module DHH.Cubical.DayHomCompositionParameterRoute where

open import Cubical.Foundations.Prelude
open import DHH.CubicalNerve
open import DHH.Cubical.DayTensor
open import DHH.Cubical.DayTriple
open import DHH.Cubical.DayHomNestedEvaluation
open import DHH.Cubical.DayHomCompositionParameter

private variable ℓ : Level

-- A separate module boundary retains only these two named maps and β
-- statements. In the proposed base version, nestedEvaluation itself is
-- abstract together with its β theorem.
abstract
  homParameterEvaluation-nested : (X Y A B C : CubicalSet ℓ)
    (F : CubicalNatural (DayTensor X B) C)
    (G : CubicalNatural (DayTensor Y A) B)
    → homParameterEvaluation X Y A B C F G
      ≡ nestedEvaluation X Y A B C F G
  homParameterEvaluation-nested X Y A B C F G =
    TripleExt.leftTripleExt X Y A C
      (homParameterEvaluation X Y A B C F G)
      (nestedEvaluation X Y A B C F G)
      (λ p q r x y a → homParameterEvaluation-β X Y A B C F G p q r x y a
        ∙ sym (nestedEvaluation-β X Y A B C F G p q r x y a))
