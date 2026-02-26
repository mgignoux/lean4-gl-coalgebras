-- Soundness1: Soundness of the basic split sequent system!

import Mathlib.Data.Finset.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import GL.Logic
import GL.Semantics
import GL.SplitCoalgebraProof
import GL.SplitCutCoalgebraProof

namespace SplitCut

open Classical in
set_option maxHeartbeats 300000 in
noncomputable def chain
  {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬Evaluate_sseq (M, w) Γ)
  (n : Nat) : (y : 𝕏.X) × {u : W // ¬ Evaluate_sseq ⟨M, u⟩ (f (r 𝕏.α y))}
    := match n with
       | 0 => ⟨x, ⟨w, by simp_all⟩⟩
       | n + 1 =>
        match chain prop w_prop n with
        | ⟨x_ih, w_ih, w_ih_prop⟩ =>
        match r_def : r 𝕏.α x_ih with
        | .skp Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have h : ¬Evaluate_sseq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.h x_ih
              simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
              convert w_ih_prop using 2
              rw [𝕏h_x_ih, r_def]
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | y :: z :: l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .cutₗ Δ φ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            if w_ih_nφ : ¬Evaluate (M, w_ih) φ
            then
              ⟨y, w_ih, by
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton, fₙ_alternate] at this
                simp [Evaluate_sseq, this.1, w_ih_nφ]
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nnφ : ¬Evaluate (M, w_ih) (~φ) := by
                  simp [Evaluate_neg]
                  tauto
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_sseq, this.2, w_ih_nnφ, fₙ_alternate]
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
        | .cutᵣ Δ φ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            if w_ih_nφ : ¬Evaluate (M, w_ih) φ
            then
              ⟨y, w_ih, by
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton, fₙ_alternate] at this
                simp [Evaluate_sseq, this.1, w_ih_nφ]
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nnφ : ¬Evaluate (M, w_ih) (~φ) := by
                  simp [Evaluate_neg]
                  tauto
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_sseq, this.2, w_ih_nnφ, fₙ_alternate]
                intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
        | .wkₗ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have h : ¬Evaluate_sseq (M, w_ih) (f (r 𝕏.α y)) := by
              have := 𝕏.h x_ih
              simp [r_def, p_def, -Finset.union_singleton, fₙ_alternate] at this
              simp [r_def, f] at w_ih_prop
              simp [this]
              tauto
            ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .wkᵣ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have h : ¬Evaluate_sseq (M, w_ih) (f (r 𝕏.α y)) := by
              have := 𝕏.h x_ih
              simp [r_def, p_def, -Finset.union_singleton, fₙ_alternate] at this
              simp [r_def, f] at w_ih_prop
              simp [this]
              tauto
            ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .topₗ Δ in_Δ => False.elim (by simp [r_def, f] at w_ih_prop; have := w_ih_prop.1 ⊤ in_Δ; simp_all)
        | .topᵣ Δ in_Δ => False.elim (by simp [r_def, f] at w_ih_prop; have := w_ih_prop.2 ⊤ in_Δ; simp_all)
        | .axₗₗ Δ n in_Δ =>
          False.elim (by
            by_cases Evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.1 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.1 (na n) in_Δ.2
              simp_all)
        | .axₗᵣ Δ n in_Δ =>
          False.elim (by
            by_cases Evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.1 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.2 (na n) in_Δ.2
              simp_all)
        | .axᵣₗ Δ n in_Δ =>
          False.elim (by
            by_cases Evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.2 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.1 (na n) in_Δ.2
              simp_all)
        | .axᵣᵣ Δ n in_Δ =>
          False.elim (by
            by_cases Evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.2 (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop.2 (na n) in_Δ.2
              simp_all)
        | .andₗ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            have := not_and_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (Sum.inl (φ₁ & φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            if w_ih_nφ₁ : ¬Evaluate (M, w_ih) φ₁
            then
              ⟨y, w_ih, by
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_sseq, this.1, w_ih_nφ₁, fₙ_alternate]
                constructor
                · intro χ χ_in χ_not con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nφ₂ : ¬Evaluate (M, w_ih) φ₂ := by simp_all
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_sseq, this.2, w_ih_nφ₂, fₙ_alternate]
                constructor
                · intro χ χ_in χ_not con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .andᵣ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            have := not_and_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (Sum.inr (φ₁ & φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            if w_ih_nφ₁ : ¬Evaluate (M, w_ih) φ₁
            then
              ⟨y, w_ih, by
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_sseq, this.1, w_ih_nφ₁, fₙ_alternate]
                constructor
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in _ con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nφ₂ : ¬Evaluate (M, w_ih) φ₂ := by simp_all
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_sseq, this.2, w_ih_nφ₂, fₙ_alternate]
                constructor
                · intro χ χ_in con
                  apply w_ih_prop
                  exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
                · intro χ χ_in _ con
                  apply w_ih_prop
                  exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .orₗ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have := not_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (Sum.inl (φ₁ v φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬Evaluate_sseq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.h x_ih
              simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
              simp [Evaluate_sseq, 𝕏h_x_ih, fₙ_alternate, this]
              constructor
              · intro χ χ_in _ con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              · intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .orᵣ Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have := not_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (Sum.inr (φ₁ v φ₂)) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬Evaluate_sseq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.h x_ih
              simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
              simp [Evaluate_sseq, 𝕏h_x_ih, fₙ_alternate, this]
              constructor
              · intro χ χ_in con
                apply w_ih_prop
                exact ⟨Sum.inl χ, r_def ▸ χ_in, con⟩
              · intro χ χ_in _ con
                apply w_ih_prop
                exact ⟨Sum.inr χ, r_def ▸ χ_in, con⟩
              ⟨y, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .boxₗ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
              have := not_forall.1 $ fun x ↦ (not_exists.1 w_ih_prop) (Sum.inl (□ φ)) ⟨(r_def ▸ in_Δ), x⟩
              let w_next := this.choose
              have w_next_prop := Classical.not_imp.1 this.choose_spec
              have h : ¬Evaluate_sseq (M, w_next) (f (r 𝕏.α y)) := by
                have 𝕏h_x_ih := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
                simp [Evaluate_sseq, 𝕏h_x_ih, fₙ_alternate]
                refine ⟨?_, ⟨?_, ?_⟩⟩
                · exact w_next_prop.2
                · simp [SplitSequent.D]
                  simp [Evaluate_sseq, r_def, f] at w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨⟨χ_in, χ_not_box_φ⟩, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.1 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.1 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
                · simp [SplitSequent.D]
                  simp [Evaluate_sseq, r_def, f] at w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨χ_in, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.2 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.2 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
              ⟨y, w_next, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
        | .boxᵣ Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
              have := not_forall.1 $ fun x ↦ (not_exists.1 w_ih_prop) (Sum.inr (□ φ)) ⟨(r_def ▸ in_Δ), x⟩
              let w_next := this.choose
              have w_next_prop := Classical.not_imp.1 this.choose_spec

              have h : ¬Evaluate_sseq (M, w_next) (f (r 𝕏.α y)) := by
                have 𝕏h_x_ih := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
                simp [Evaluate_sseq, 𝕏h_x_ih, fₙ_alternate]
                refine ⟨?_, ⟨?_, ?_⟩⟩
                · exact w_next_prop.2
                · simp [SplitSequent.D]
                  simp [Evaluate_sseq, r_def, f] at w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨χ_in, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.1 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.1 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
                · simp [SplitSequent.D]
                  simp [Evaluate_sseq, r_def, f] at w_ih_prop
                  intro χ χ_in con
                  rcases χ_in with ⟨⟨χ_in, χ_not_box_φ⟩, χ_di⟩ | diχ_Δ
                  · apply w_ih_prop.2 _ χ_in
                    cases χ <;> simp [SplitFormula.isDiamond] at χ_di
                    case diamond χ' =>
                      have ⟨u, w_next_u, u_χ'⟩ := con
                      exact ⟨u, M.trans w_next_prop.1 w_next_u, u_χ'⟩
                  · exact w_ih_prop.2 _ diχ_Δ ⟨w_next, w_next_prop.1, con⟩
              ⟨y, w_next, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

set_option maxHeartbeats 40000000
lemma chain_proof_prop
  {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬Evaluate_sseq (M, w) Γ)
  : ∀ n, edge 𝕏.α (chain prop w_prop n).1 (chain prop w_prop (n + 1)).1 := by
    intro n
    conv =>
      congr
      · skip
      · skip
      · unfold chain
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    cases r 𝕏.α (chain prop w_prop n).fst <;> grind [edge]

lemma chain_model_prop {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬Evaluate_sseq (M, w) Γ)
  : ∀ n, (¬ (r 𝕏.α (chain prop w_prop n).1).isBox →     (chain prop w_prop n).2.1 = (chain prop w_prop (n + 1)).2.1)
       ∧ (  (r 𝕏.α (chain prop w_prop n).1).isBox → M.R (chain prop w_prop n).2.1   (chain prop w_prop (n + 1)).2.1)
  := by
  intro n
  constructor
  · conv =>
      congr
      · skip
      · conv =>
          congr
          · skip
          · rw [chain] -- I think Subtype.val might be preventing from unfolding chain
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩ -- when you do split directly after this it 'redoes' this
    simp
    split <;> grind [RuleApp.isBox]
  · conv =>
      congr
      · skip
      · conv =>
          congr
          · skip
          · skip
          · rw [chain] -- I think Subtype.val might be preventing from unfolding chain
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩ -- when you do split directly after this it 'redoes' this
    simp
    split <;> try grind [RuleApp.isBox]

theorem has_children_of_chain_model {𝕏 : Proof}
  {x : 𝕏.X}
  {Γ : SplitSequent}
  (prop : f (r 𝕏.α x) = Γ)
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬Evaluate_sseq (M, w) Γ) :
  ∀ n, ∃ m, M.R (chain prop w_prop n).2.1 (chain prop w_prop (n + m)).2.1 := by
  intro n
  by_contra h
  simp at h
  have g1 : ∀ m, (chain prop w_prop n).2.1 = (chain prop w_prop (n + m)).2.1 := by
    intro m
    induction m
    · rfl
    case succ k ih =>
      simp only [ih] at *
      have h := h (k + 1)
      have chain_model_prop := chain_model_prop prop w_prop (n + k)
      by_cases (r 𝕏.α (chain prop w_prop (n + k)).fst).isBox
      case pos box =>
        simp [box] at chain_model_prop
        exfalso
        exact h chain_model_prop
      case neg nbox =>
        simp [nbox] at chain_model_prop
        exact chain_model_prop
  have g2 : ∀ m, ¬ (r 𝕏.α (chain prop w_prop (n + m)).fst).isBox := by
    intro m con
    have eq1 := g1 m
    have eq2 := g1 (m + 1)
    rw [eq1] at eq2
    have chain_model_prop := chain_model_prop prop w_prop (n + m)
    simp [con] at chain_model_prop
    rw [eq2, add_assoc] at chain_model_prop
    apply (instModelIsIrref M).irrefl _ chain_model_prop
  have ⟨k, k_prop⟩ := 𝕏.path x ⟨(fun n ↦ (chain prop w_prop n).1), ⟨by simp [chain], chain_proof_prop prop w_prop⟩⟩ n
  exact g2 k k_prop

/- Below are copied! -/
noncomputable
def inc_chain_eventual_inc_chain {β}
  {Q : β → β → Prop}
  {g : ℕ → β}
  (Q_prop : ∀ n, ∃ m, Q (g n) (g m))
  (n : ℕ) : {b : β // ∃ n, b = g n} :=
  match n with
   | 0 => ⟨g (Q_prop 0).choose, by simp⟩
   | n + 1 =>
      match inc_chain_eventual_inc_chain Q_prop n with
        | ⟨ih, ih_prop⟩ => ⟨g (Q_prop ih_prop.choose).choose, by simp⟩

theorem inc_chain_eventual_inc_chain_prop {β}
  {Q : β → β → Prop} {g : ℕ → β}
  (Q_prop : ∀ n, ∃ m, Q (g n) (g m)) :
  ∀ n, Q (inc_chain_eventual_inc_chain Q_prop n).1
         (inc_chain_eventual_inc_chain Q_prop (n + 1)).1
   := by
    intro n
    conv =>
      congr
      · skip
      · unfold inc_chain_eventual_inc_chain
    rcases inc_chain_eventual_inc_chain Q_prop n with ⟨ih, ih_prop⟩
    simp
    have := (Q_prop ih_prop.choose).choose_spec
    convert this
    · exact ih_prop.choose_spec

theorem Soundness (Γ : SplitSequent) : SplitSequent.isTrue Γ → ⊨ Γ := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  by_contra h
  simp only [SplitSequent.isValid, not_forall] at h
  have ⟨W, M, w, w_prop⟩ := h
  apply (wellFounded_iff_isEmpty_descending_chain.1 M.con_wf).false
  use fun k ↦ (@inc_chain_eventual_inc_chain _ M.R (fun n ↦ (chain prop w_prop n).2.1)
    (by
      intro n
      have ⟨m, m_prop⟩ := has_children_of_chain_model prop w_prop n
      use n + m) k).1
  exact fun k ↦ @inc_chain_eventual_inc_chain_prop _ M.R (fun n ↦ (chain prop w_prop n).2.1)
    (by
      intro n
      have ⟨m, m_prop⟩ := has_children_of_chain_model prop w_prop n
      use n + m) k

-- we may want to adapt this to the most complex split sequent system! because a proof in this system will be a proof in that system, so we get soundness for free

-- we wanat completeness for this system because a proof in this system is a proof in the more complex system !

end SplitCut

@[simp]
def α_conv (𝕏 : Split.Proof) : 𝕏.X → SplitCut.T.obj 𝕏.X := fun x ↦
  match Split.r 𝕏.α x with
    | .topₗ Δ in_Δ => ⟨.topₗ Δ in_Δ, Split.p 𝕏.α x⟩
    | .topᵣ Δ in_Δ => ⟨.topᵣ Δ in_Δ, Split.p 𝕏.α x⟩
    | .axₗₗ Δ n in_Δ => ⟨.axₗₗ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .axₗᵣ Δ n in_Δ => ⟨.axₗᵣ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .axᵣₗ Δ n in_Δ => ⟨.axᵣₗ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .axᵣᵣ Δ n in_Δ => ⟨.axᵣᵣ Δ n in_Δ, Split.p 𝕏.α x⟩
    | .andₗ Δ φ ψ in_Δ => ⟨.andₗ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .andᵣ Δ φ ψ in_Δ => ⟨.andᵣ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .orₗ Δ φ ψ in_Δ => ⟨.orₗ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .orᵣ Δ φ ψ in_Δ => ⟨.orᵣ Δ φ ψ in_Δ, Split.p 𝕏.α x⟩
    | .boxₗ Δ φ in_Δ => ⟨.boxₗ Δ φ in_Δ, Split.p 𝕏.α x⟩
    | .boxᵣ Δ φ in_Δ => ⟨.boxᵣ Δ φ in_Δ, Split.p 𝕏.α x⟩

-- If there is a Split proof then there is a SplitCut proof
theorem SplitProofIsSplitCutProof (Γ : SplitSequent) : (Split.SplitSequent.isTrue Γ) → (SplitCut.SplitSequent.isTrue Γ) := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  have := 𝕏.X
  use {
    X := 𝕏.X
    α := α_conv 𝕏
    h x := by
      have helper : ∀ x, SplitCut.f (SplitCut.r (α_conv 𝕏) x) = Split.f (Split.r 𝕏.α x) := by
        intro x
        cases r_def : Split.r 𝕏.α x <;> simp_all only [α_conv, SplitCut.r, SplitCut.f, Split.f]
      have := 𝕏.h x
      cases r_def : Split.r 𝕏.α x <;> simp_all only [α_conv, SplitCut.r, SplitCut.p, Split.fₙ_alternate, SplitCut.fₙ_alternate]
    path x := by
      have h : ∀ x, (SplitCut.r (α_conv 𝕏) x).isBox ↔ (Split.r 𝕏.α x).isBox := by
        intro x
        cases r_def : Split.r 𝕏.α x <;> simp_all only [α_conv, SplitCut.r, SplitCut.RuleApp.isBox, Split.RuleApp.isBox]
      simp [h]
      intro f base step n
      apply Split.inf_path_has_inf_boxes f ?_ n
      convert step
      unfold SplitCut.edge Split.edge α_conv
      simp [SplitCut.p]
      grind
    }
  use x
  simp [←prop]
  cases r_def : Split.r 𝕏.α x <;> simp_all only [α_conv, SplitCut.r, SplitCut.f, Split.f]

namespace Split

theorem Soundness (Γ : SplitSequent) : SplitSequent.isTrue Γ → ⊨ Γ := by
  intro mp
  exact SplitCut.Soundness Γ (SplitProofIsSplitCutProof Γ mp)
