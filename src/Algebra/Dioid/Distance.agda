module Algebra.Dioid.Distance where

  open import Algebra.Nat
  open import Reasoning.Equality
  open import Reasoning.Equational

  data Distance : Set where
    hop   : ℕ → Distance
    nohop :     Distance

  _∨_ : Distance → Distance → Distance
  hop x ∨ hop y = hop (min x y)
  a ∨ nohop = a
  nohop ∨ b = b

  _∧_ : Distance → Distance → Distance
  hop x ∧ hop y = hop (x + y)
  a ∧ nohop = nohop
  nohop ∧ b = nohop

  lemma-n-implies-distance : {x y : ℕ} → x ≡ y → hop x ≡ hop y
  lemma-n-implies-distance refl = refl
  lemma-n-implies-distance (symm p) = symm (lemma-n-implies-distance p)
  lemma-n-implies-distance (trans p q) =
    trans (lemma-n-implies-distance p) (lemma-n-implies-distance q)
