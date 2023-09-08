module Algebra.Dioid.Distance where

  open import Algebra.Nat
  open import Reasoning.Equality
  open import Reasoning.Equational

  -- Two nodes in a graph are either connected trough a path
  --      ∘ ­³­ ∘   which has weight 3 (in this case)
  -- or are in two separate components
  --      ∘     ∘
  data Distance : Set where
    hop   : ℕ → Distance      --      ∘ ­ⁿ­ ∘
    nohop :     Distance      --      ∘     ∘

  -- The intended meaning of the ∨ operator is choosing between two
  -- possible paths from a node to another one: in this case we prefer
  -- the shortest possible path
  
  --      /⁻⁻⁻⁵⁻⁻⁻\ 
  --     ∘ ---²--- ∘    ← the bottom one is shorter
  _∨_ : Distance → Distance → Distance
  hop x ∨ hop y = hop (min x y)
  a ∨ nohop = a
  nohop ∨ b = b

  -- The intended meaning of the ∧ operator is connecting two paths
  -- together: in this case the resulting path length will be the sum
  -- of the lengths of the two paths we're joining

  --  ∘ --³- ∘ ---⁷--- ∘     ← the resulting path has length (3 + 7) = 10
  _∧_ : Distance → Distance → Distance
  hop x ∧ hop y = hop (x + y)
  a ∧ nohop = nohop
  nohop ∧ b = nohop

  -- If two numbers are the same, the distance they identify is the
  -- same
  lemma-n-implies-distance : {x y : ℕ} → x ≡ y → hop x ≡ hop y
  lemma-n-implies-distance refl = refl
  lemma-n-implies-distance (symm p) = symm (lemma-n-implies-distance p)
  lemma-n-implies-distance (trans p q) =
    trans (lemma-n-implies-distance p) (lemma-n-implies-distance q)
