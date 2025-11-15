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
  con_wf : WellFounded (fun x y ↦ R y x)

lemma Model.Irreflexive {α : Type} (M : Model α) : ∀ a b, a = b → ¬ M.R a b := by sorry

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

instance decEval {α : Type} {M : Model α} {u : α} {φ : Formula} : Decidable (Evaluate ⟨M, u⟩ φ) := by sorry

@[simp]
def Evaluate_seq {α : Type} : Model α × α → Sequent → Prop :=
  λ M_u Γ ↦ ∃ φ ∈ Γ, Evaluate M_u φ

def isValid (φ : Formula) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, Evaluate ⟨M, u⟩ φ

prefix:40 "⊨" => isValid
