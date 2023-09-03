module Algebra.Dioid.Distance.Theorems where

  open import Algebra.Dioid
  open import Algebra.Nat
  open import Algebra.Dioid.Distance
  open import Reasoning.Equality
  open import Reasoning.Equational

  ∨-left-congruence : ∀ {b c d : Distance} → b ≡ c → (b ∨ d) ≡ (c ∨ d)
  ∨-left-congruence {b} {c} {d} p = begin
    b ∨ d ≡⟨ cong (λ x → x ∨ d) p ⟩
    c ∨ d ∎
    
  ∨-right-congruence : ∀ {b c d : Distance} → c ≡ d → (b ∨ c) ≡ (b ∨ d)
  ∨-right-congruence {b} {c} {d} p = begin
    b ∨ c ≡⟨ cong (_∨_ b) p ⟩
    b ∨ d ∎
    
  ∧-left-congruence : ∀ {b c d : Distance} → b ≡ c → (b ∧ d) ≡ (c ∧ d)
  ∧-left-congruence {b} {c} {d} p = begin
    b ∧ d ≡⟨ cong (λ x → x ∧ d) p ⟩
    c ∧ d ∎
    
  ∧-right-congruence : ∀ {b c d : Distance} → c ≡ d → (b ∧ c) ≡ (b ∧ d)
  ∧-right-congruence {b} {c} {d} p = begin
    b ∧ c ≡⟨ cong (_∧_ b) p ⟩
    b ∧ d ∎
    
  ∨-idempotence : ∀ {b : Distance} → (b ∨ b) ≡ b
  ∨-idempotence {hop x}  = lemma-n-implies-distance (lemma-min-idempotence x)
  ∨-idempotence {nohop} = refl

  ∨-unreach-identity : ∀ {b : Distance} → (b ∨ nohop) ≡ b
  ∨-unreach-identity {hop x}  = refl
  ∨-unreach-identity {nohop} = refl

  ∨-unreach-identity-left : ∀ {b : Distance} → (nohop ∨ b) ≡ b
  ∨-unreach-identity-left {hop x}  = refl
  ∨-unreach-identity-left {nohop} = refl
    
  ∨-commutativity : ∀ {r s : Distance} → (r ∨ s) ≡ (s ∨ r)
  ∨-commutativity {hop x} {hop y} = lemma-n-implies-distance (lemma-min-commutativity y x)
  ∨-commutativity {hop x} {nohop} = refl
  ∨-commutativity {nohop} {s} = begin
    nohop ∨ s ≡⟨ ∨-unreach-identity-left ⟩
    s               ≡⟨ symm ∨-unreach-identity ⟩
    s ∨ nohop ∎

  ∨-associativity : ∀ {b c d : Distance} → (b ∨ (c ∨ d)) ≡ ((b ∨ c) ∨ d)
  ∨-associativity {hop x} {hop y} {hop z}   = lemma-n-implies-distance (lemma-min-associative x y z)
  ∨-associativity {hop x} {nohop} {hop z}  = refl
  ∨-associativity {nohop} {hop y} {hop z}  = refl
  ∨-associativity {nohop} {nohop} {hop z} = refl
  ∨-associativity {b} {c} {nohop} = begin
    b ∨ (c ∨ nohop) ≡⟨ cong (_∨_ b) ∨-unreach-identity ⟩
    b ∨ c                 ≡⟨ symm ∨-unreach-identity ⟩
    (b ∨ c) ∨ nohop ∎

  ∧-left-unreach : ∀ {b : Distance} → (nohop ∧ b) ≡ nohop
  ∧-left-unreach {hop x} = refl
  ∧-left-unreach {nohop} = refl
  
  ∧-right-unreach : ∀ {b : Distance} → (b ∧ nohop) ≡ nohop
  ∧-right-unreach {hop x} = refl
  ∧-right-unreach {nohop} = refl
  
  ∧-associativity : ∀ {b c d : Distance} → (b ∧ (c ∧ d)) ≡ ((b ∧ c) ∧ d)
  ∧-associativity {hop x} {hop y} {hop z} = lemma-n-implies-distance (lemma-+-associative x y z)
  ∧-associativity {nohop} {c} {d} = begin
    nohop ∧ (c ∧ d) ≡⟨ ∧-left-unreach ⟩
    nohop           ≡⟨ symm ∧-left-unreach ⟩
    nohop ∧ d       ≡⟨ cong (λ x → (x ∧ d)) (symm ∧-left-unreach) ⟩
    (nohop ∧ c) ∧ d ∎
  ∧-associativity {b} {nohop} {d} = begin
    b ∧ (nohop ∧ d)  ≡⟨ cong (_∧_ b) ∧-left-unreach ⟩
    b ∧ nohop        ≡⟨ ∧-right-unreach ⟩
    nohop            ≡⟨ symm ∧-left-unreach ⟩ 
    nohop ∧ d        ≡⟨ cong (λ x → x ∧ d) (symm ∧-right-unreach) ⟩
    (b ∧ nohop) ∧ d ∎
  ∧-associativity {b} {c} {nohop} = begin
    b ∧ (c ∧ nohop) ≡⟨ cong (_∧_ b) ∧-right-unreach ⟩
    b ∧ nohop       ≡⟨ ∧-right-unreach ⟩
    nohop           ≡⟨ symm ∧-right-unreach ⟩
    (b ∧ c) ∧ nohop ∎
    
  ∧-left-dist-zero : ∀ {b : Distance} → (hop zero ∧ b) ≡ b
  ∧-left-dist-zero {hop x}  = refl
  ∧-left-dist-zero {nohop} = refl
    
  ∧-right-dist-zero : ∀ {b : Distance} → (b ∧ hop zero) ≡ b
  ∧-right-dist-zero {hop x}  = lemma-n-implies-distance (lemma-+-zero x)
  ∧-right-dist-zero {nohop} = refl
    
  left-distributivity : ∀ {b c d : Distance} → (b ∧ (c ∨ d)) ≡ ((b ∧ c) ∨ (b ∧ d))
  left-distributivity {hop x} {hop y} {hop z}    = lemma-n-implies-distance (distributivity-min-right x y z)
  left-distributivity {hop x} {hop y} {nohop}   = refl
  left-distributivity {hop x} {nohop} {hop z}   = refl
  left-distributivity {hop x} {nohop} {nohop}  = refl
  left-distributivity {nohop} {hop y} {hop z}   = refl
  left-distributivity {nohop} {hop y} {nohop}  = refl
  left-distributivity {nohop} {nohop} {hop z}  = refl
  left-distributivity {nohop} {nohop} {nohop} = refl
    
  right-distributivity : ∀ {b c d : Distance} → ((b ∨ c) ∧ d) ≡ ((b ∧ d) ∨ (c ∧ d))
  right-distributivity {hop x} {hop y} {hop z} = lemma-n-implies-distance (distributivity-min-left x y z)
  right-distributivity {nohop} {c} {d} = begin
    (nohop ∨ c) ∧ d       ≡⟨ cong (λ x → x ∧ d) ∨-unreach-identity-left ⟩
    c ∧ d                       ≡⟨ symm ∨-unreach-identity-left ⟩
    nohop ∨ (c ∧ d)       ≡⟨ cong (λ x → x ∨ (c ∧ d)) (symm (∧-left-unreach {d})) ⟩
    (nohop ∧ d) ∨ (c ∧ d) ∎
  right-distributivity {b} {nohop} {d} = begin
    (b ∨ nohop) ∧ d       ≡⟨ cong (λ x → x ∧ d) ∨-unreach-identity ⟩
    b ∧ d                       ≡⟨ symm ∨-unreach-identity ⟩
    (b ∧ d) ∨ nohop       ≡⟨ cong (_∨_ (b ∧ d)) (symm (∧-left-unreach {d})) ⟩
    (b ∧ d) ∨ (nohop ∧ d) ∎
  right-distributivity {b} {c} {nohop} = begin
    (b ∨ c) ∧ nohop                 ≡⟨ ∧-right-unreach ⟩
    nohop ∨ nohop             ≡⟨ cong (_∨_ nohop) (symm (∧-right-unreach {c})) ⟩
    nohop ∨ (c ∧ nohop)       ≡⟨ cong (λ x → x ∨ (c ∧ nohop)) (symm (∧-right-unreach {b})) ⟩
    (b ∧ nohop) ∨ (c ∧ nohop) ∎

  shortest-distance-dioid : Dioid Distance _≡_
  shortest-distance-dioid = record
    { zero = nohop
    ; one  = hop zero
    ; _+_  = _∨_
    ; _*_  = _∧_
    ; reflexivity  = refl
    ; symmetry     = symm
    ; transitivity = trans
  
    ; +left-congruence  = ∨-left-congruence
    ; *left-congruence  = ∧-left-congruence
    ; *right-congruence = ∧-right-congruence

    ; +idempotence   = ∨-idempotence
    ; +commutativity = λ {x} {y} → ∨-commutativity {x} {y}
    ; +associativity = λ {x} {y} {z} → ∨-associativity {x} {y} {z}
    ; +zero-identity = ∨-unreach-identity
  
    ; *associativity  = ∧-associativity
    ; *left-zero      = ∧-left-unreach
    ; *right-zero     = ∧-right-unreach
    ; *left-identity  = ∧-left-dist-zero
    ; *right-identity = ∧-right-dist-zero
  
    ; left-distributivity  = left-distributivity
    ; right-distributivity = λ {x} {y} {z} → right-distributivity {x} {y} {z}
    }
