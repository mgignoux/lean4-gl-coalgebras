import Mathlib.Data.Finset.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import GL.Logic


/- GL Model -/
structure Model (α : Type) : Type where
  V : α → Nat → Prop
  R : α → α → Prop
  trans : Transitive R
  con_wf : WellFounded (Function.swap R)

instance instModelIsIrref {α : Type} (M : Model α) : IsIrrefl α M.R where
  irrefl := fun a con ↦ (WellFounded.isIrrefl M.con_wf).irrefl a con

@[simp]
def Evaluate {α : Type} : Model α × α → Formula → Prop
  | (_, _), ⊥ => False
  | (_, _), ⊤ => True
  | (M, w), at n => M.V w n
  | (M, w), na n => ¬ M.V w n
  | (M, w), φ & ψ => Evaluate (M, w) φ ∧ Evaluate (M, w) ψ
  | (M, w), φ v ψ => Evaluate (M, w) φ ∨ Evaluate (M, w) ψ
  | (M, w), □ φ => ∀ (u : α), M.R w u → Evaluate (M, u) φ
  | (M, w), ◇ φ => ∃ (u : α), M.R w u ∧ Evaluate (M, u) φ

theorem Evaluate_neg {α : Type} (M : Model α) (u : α) (φ : Formula) : ¬ Evaluate (M, u) φ ↔ Evaluate (M, u) (~φ) := by
  induction φ generalizing u <;> simp [Formula.neg, Evaluate] <;> grind

@[simp]
theorem Evaluate_and {α : Type} (M : Model α) (u : α) (φ ψ : Formula) : Evaluate (M, u) (φ & ψ) ↔ (Evaluate (M, u) φ ∧ Evaluate (M, u) ψ) := by
  simp

@[simp]
theorem Evaluate_imp {α : Type} (M : Model α) (u : α) (φ ψ : Formula) : Evaluate (M, u) (φ ↣ ψ) ↔ (Evaluate (M, u) φ → Evaluate (M, u) ψ) := by
  simp [←Evaluate_neg]
  tauto

-- @[simp]
-- theorem Evaluate_imp' {α : Type} (M : Model α) (u : α) (φ ψ : Formula) : Evaluate (M, u) (~ φ v ψ) ↔ (Evaluate (M, u) φ → Evaluate (M, u) ψ) := by
--   simp [←Evaluate_neg]
--   tauto

@[simp]
def Evaluate_seq {α : Type} : Model α × α → Sequent → Prop :=
  λ M_u Γ ↦ ∃ φ ∈ Γ, Evaluate M_u φ

@[simp]
def Evaluate_sseq {α : Type} : Model α × α → SplitSequent → Prop :=
  λ M_u Γ ↦ ∃ φ ∈ Γ, Evaluate M_u (Sum.elim id id φ)

def Formula.isValid (φ : Formula) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, Evaluate ⟨M, u⟩ φ

def Sequent.isValid (Δ : Sequent) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, Evaluate_seq ⟨M, u⟩ Δ

def SplitSequent.isValid (Δ : SplitSequent) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, Evaluate_sseq ⟨M, u⟩ Δ

prefix:40 "⊨" => Formula.isValid
prefix:40 "⊨" => Sequent.isValid
prefix:40 "⊨" => SplitSequent.isValid

def sem_equiv : Formula → Formula → Prop := fun φ ψ ↦ ⊨ φ ⟷ ψ

/- TRANSFORMATIONS -/

/-- Structure preserving map substituting Pₙ by C --/
def single (n : Nat) (C : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at k => if k == n then C else at k
  | na k => if k == n then ~ C else na k
  | A & B => (single n C A) & (single n C B)
  | A v B => (single n C A) v (single n C B)
  | □ A => □ (single n C A)
  | ◇ A => ◇ (single n C A)

theorem single_neg (n : Nat) (C D : Formula) : single n C (~D) = Formula.neg (single n C D) := by
  induction D <;> simp [Formula.neg, single]
  case neg_atom m =>
    by_cases m = n
    case pos h => simp [h]
    case neg h => simp [h]
  all_goals
    aesop

theorem single_iff (n : Nat) (C D E : Formula) : single n C (D ⟷ E) = (single n C D) ⟷ (single n C E) := by
  simp [single, single_neg]

@[simp]
theorem in_neg_voc_iff {n : Nat} {φ : Formula} : n ∈ (~φ).vocab ↔ n ∈ φ.vocab := by
  induction φ <;> simp_all [Formula.vocab]

theorem in_single_voc (m n : Nat) (φ ψ : Formula) :
  m ∉ φ.vocab → (m ≠ n → m ∉ ψ.vocab) → n ∉ φ.vocab → m ∉ (single n φ ψ).vocab
  := by
    intro mp
    induction ψ <;> simp_all [single, Formula.vocab]
    case atom k =>
      by_cases k = n <;> simp_all [Formula.vocab]; aesop
    case neg_atom k =>
      by_cases k = n <;> simp_all [Formula.vocab]
      aesop

/-- Structure preserving map substituting all atoms meeting a certain criteria p --/
def partial_ {p : Nat → Prop} [DecidablePred p] (σ : Subtype p → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : p n then σ ⟨n, h⟩ else at n
  | na n => if h : p n then ~ σ ⟨n, h⟩ else na n
  | A & B => (partial_ σ A) & (partial_ σ B)
  | A v B => (partial_ σ A) v (partial_ σ B)
  | □ A => □ (partial_ σ A)
  | ◇ A => ◇ (partial_ σ A)

/-- Structure preserving map substituting all atoms via a transformation σ --/
def full (σ : Nat → Formula) (A : Formula) : Formula := match A with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => σ n
  | na n => ~ (σ n)
  | A & B => (full σ A) & (full σ B)
  | A v B => (full σ A) v (full σ B)
  | □ A => □ (full σ A)
  | ◇ A => ◇ (full σ A)
termination_by Formula.size A
decreasing_by
  all_goals
  simp [Formula.size]
  try linarith

def Substitution {α} (M : Model α) (n : Nat) (φ : Formula) : Model α where
  V u k := if n = k then Evaluate ⟨M, u⟩ φ else M.V u k
  R := M.R
  trans := M.trans
  con_wf := M.con_wf

/- Substitution Lemma -/
theorem Substitution_Lemma {α} (M : Model α) (u : α) (n : Nat) (ψ : Formula)
  : ∀ φ, Evaluate ⟨M, u⟩ (single n ψ φ) ↔ Evaluate ⟨(Substitution M n ψ), u⟩ φ := by
  intro φ
  induction φ generalizing u <;> simp_all [single, Substitution] <;> try grind
  case atom k => aesop
  case neg_atom k => if eq : k = n then simp [eq, Evaluate_neg] else aesop

open Classical in
theorem single_preserves_validity (n : Nat) (φ ψ : Formula) : ⊨ φ → ⊨ single n ψ φ := by
  intro φ_val α M u
  exact (Substitution_Lemma M u n ψ φ).2 (φ_val α (Substitution M n ψ) u)

theorem single_preserves_sem_equiv (n : Nat) (χ φ ψ : Formula)
    (φ_equiv_ψ : ⊨ φ ⟷ ψ) : ⊨ (single n χ φ) ⟷ (single n χ ψ) := by
  convert single_preserves_validity n (φ ⟷ ψ) χ φ_equiv_ψ using 1
  simp [single_iff]
