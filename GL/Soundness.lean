import Mathlib.Data.Finset.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import GL.Logic
import GL.Semantics
import GL.CoalgebraProof

noncomputable def chain
  {𝕏 : Proof}
  {x : 𝕏.X}
  {φ : Formula}
  (prop : f (r 𝕏.α x) = {φ})
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬Evaluate (M, w) φ)
  (n : Nat) : (y : 𝕏.X) × {u : W // ¬ Evaluate_seq ⟨M, u⟩ (f (r 𝕏.α y))}
    := match n with
       | 0 => ⟨x, ⟨w, by simp_all⟩⟩
       | n + 1 =>
        match chain prop w_prop n with
        | ⟨x_ih, w_ih, w_ih_prop⟩ =>
        match r_def : r 𝕏.α x_ih with
        | .top Δ in_Δ => False.elim (by simp [r_def, f] at w_ih_prop; have := w_ih_prop ⊤ in_Δ; simp_all)
        | .ax Δ n in_Δ =>
          False.elim (by
            by_cases Evaluate ⟨M, w_ih⟩ (at n)
            case pos w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop (at n) in_Δ.1
              simp_all
            case neg not_w_n =>
              simp [r_def, f] at w_ih_prop
              have := w_ih_prop (na n) in_Δ.2
              simp_all)
        | .and Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y,z] =>
            have := not_and_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (φ₁ & φ₂) ⟨(r_def ▸ in_Δ), x⟩
            if w_ih_nφ₁ : ¬Evaluate (M, w_ih) φ₁
            then
              ⟨y, w_ih, by
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_seq, this.1, w_ih_nφ₁, fₙ_alternate]
                intro χ χ_in χ_not con
                apply w_ih_prop
                exact ⟨χ, r_def ▸ χ_in, con⟩
              ⟩
            else
              ⟨z, w_ih, by
                have w_ih_nφ₂ : ¬Evaluate (M, w_ih) φ₂ := by simp_all
                have := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at this
                simp [Evaluate_seq, this.2, w_ih_nφ₂, fₙ_alternate]
                intro χ χ_in χ_not con
                apply w_ih_prop
                exact ⟨χ, r_def ▸ χ_in, con⟩
              ⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .or Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
            have := not_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (φ₁ v φ₂) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬Evaluate_seq (M, w_ih) (f (r 𝕏.α y)) := by
              have 𝕏h_x_ih := 𝕏.h x_ih
              simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
              simp [Evaluate_seq, 𝕏h_x_ih, fₙ_alternate, this]
              intro χ χ_in χ_not con
              apply w_ih_prop
              exact ⟨χ, r_def ▸ χ_in, con⟩
              ⟨y, w_ih, h⟩

          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .box Δ φ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] =>
              have := not_forall.1 $ fun x ↦ (not_exists.1 w_ih_prop) (□ φ) ⟨(r_def ▸ in_Δ), x⟩
              let w_next := this.choose
              have w_next_prop := Classical.not_imp.1 this.choose_spec

              have h : ¬Evaluate_seq (M, w_next) (f (r 𝕏.α y)) := by
                have 𝕏h_x_ih := 𝕏.h x_ih
                simp [r_def, p_def, -Finset.union_singleton] at 𝕏h_x_ih
                simp [Evaluate_seq, 𝕏h_x_ih, fₙ_alternate]
                constructor
                · exact w_next_prop.2
                · simp [D]
                  intro χ χ_in
                  sorry

              ⟨y, w_next, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

lemma chain_prop   {𝕏 : Proof}
  {x : 𝕏.X}
  {φ : Formula}
  (prop : f (r 𝕏.α x) = {φ})
  {W : Type}
  {M : Model W}
  {w : W}
  (w_prop : ¬Evaluate (M, w) φ)
  : ∀ n, edge 𝕏.α (chain prop w_prop n).1 (chain prop w_prop (n + 1)).1 := by
    intro n
    -- rcases n with _ | k
    conv =>
      congr
      · skip
      · skip
      · unfold chain
    simp only [Evaluate_seq, dite_not, Classical.not_imp]
    rcases chain prop w_prop n with ⟨x_ih, w_ih, w_ih_prop⟩
    simp only
    cases r 𝕏.α (chain prop w_prop n).fst
    all_goals
      grind [edge]

theorem Soundness (φ : Formula) : ⊢ φ → ⊨ φ := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  by_contra h
  simp [isValid] at h
  have ⟨W, M, w, w_prop⟩ := h
  sorry
