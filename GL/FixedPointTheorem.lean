import GL.Semantics

def Formula.modalized (n : Nat) : Formula → Bool
  | ⊤ => False
  | ⊥ => False
  | at _ => False
  | na _ => False
  | φ & ψ => modalized n φ ∧ modalized n ψ
  | φ v ψ => modalized n φ ∧ modalized n ψ
  | □ _ => True
  | ◇ _ => True

axiom FixedPointTheorem (φ : Formula) (n : ℕ) (n_modal_in_φ : φ.modalized n) : ∃ (ψ : Formula),
  n ∉ Formula.vocab ψ ∧ sem_equiv ψ (single n ψ φ) ∧ Formula.vocab ψ ⊆ Formula.vocab φ
