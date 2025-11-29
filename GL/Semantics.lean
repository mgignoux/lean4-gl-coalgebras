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

@[simp]
def Evaluate_seq {α : Type} : Model α × α → Sequent → Prop :=
  λ M_u Γ ↦ ∃ φ ∈ Γ, Evaluate M_u φ

def isValid (φ : Formula) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, Evaluate ⟨M, u⟩ φ

def Sequent.isValid (Δ : Sequent) : Prop
  := ∀ (α : Type), ∀ M : Model α, ∀ u : α, Evaluate_seq ⟨M, u⟩ Δ

prefix:40 "⊨" => Formula.isValid
prefix:40 "⊨" => Sequent.isValid

class gen_submodel_around_form {α β} (M : Model α) (N : Model β) (φ : Formula) where
  f : β → α
  f_inf : Function.Injective f
  f_pres_val : ∀ n ∈ φ.atoms, ∀ b, N.V b n ↔ M.V (f b) n
  f_pres_rel : ∀ b1 b2, N.R b1 b2 ↔ M.R (f b1) (f b2)
  up_closed : ∀ b, ∀ a, M.R (f b) a → ∃ b', a = f b'

theorem gen_submodel_preserves_not_eval {α β} {M : Model α} {N : Model β} {φ : Formula} [inj : gen_submodel_around_form M N φ] :
  ∀ b, ∀ ψ ∈ φ.FL, ¬ Evaluate ⟨N, b⟩ ψ → ¬ Evaluate ⟨M, inj.f b⟩ ψ := by
  intro b ψ ψ_in mp con
  induction ψ generalizing b <;> simp_all only [Evaluate, not_not]
  case atom n =>
    apply mp
    exact (inj.f_pres_val n (by sorry) b).2 con
  case neg_atom n =>
    apply con
    exact (inj.f_pres_val n (by sorry) b).1 mp
  case and ih1 ih2 =>
    apply mp
    have := ih1 b (by sorry)
    have := ih2 b (by sorry)
    grind
  case or ih1 ih2 =>
    apply mp
    have := ih1 b (by sorry)
    have := ih2 b (by sorry)
    grind
  case box φ' ih =>
    simp_all
    have ⟨b', b_b', b'_φ⟩ := mp
    have fb_fb' := (inj.f_pres_rel b b').1 b_b'
    apply ih b' (by sorry) b'_φ
    exact con _ fb_fb'
  case diamond => sorry



-- theorem gen_submodel_preserves_eval {α β} {M : Model α} {N : Model β} [inj : gen_submodel M N] :
--   ∀ φ, ∀ b, Evaluate ⟨N, b⟩ φ → Evaluate ⟨M, inj.f b⟩ φ := by
--   intro φ b mp
--   induction φ generalizing b <;> simp_all
--   case atom n => exact (inj.f_pres_val b n).1 mp
--   case neg_atom n =>
--     intro con
--     apply mp
--     exact (inj.f_pres_val b n).2 con
--   case box φ ih =>
--     intro a fb_a
--     have ⟨b', a_eq_fb'⟩ := inj.f_for b a fb_a
--     subst_eqs
--     have b_b' := (inj.f_pres_rel b b').2 fb_a
--     have := mp b' b_b'
--     exact ih b' this
--   case diamond φ ih =>
--     have ⟨b', b_b', b'_φ⟩ := mp
--     have := ih b' b'_φ
--     have b_b' := (inj.f_pres_rel b b').1 b_b'
--     refine ⟨_, b_b', this⟩
--   case or => grind

-- theorem gen_submodel_preserves_valid {α β} (M : Model α) (N : Model β) [inj : gen_submodel M N] :
--   ∀ Γ, ∀ b, Evaluate_seq ⟨N, b⟩ Γ → Evaluate_seq ⟨M, inj.f b⟩ Γ := by
--   intro Γ b b_Γ
--   have ⟨φ, φ_in, b_φ⟩ := b_Γ
--   refine ⟨φ, φ_in, ?_⟩
--   exact gen_submodel_preserves_eval φ b b_φ
