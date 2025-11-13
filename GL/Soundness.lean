import Mathlib.Data.Finset.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import GL.Logic
import GL.Semantics
import GL.CoalgebraProof

set_option maxHeartbeats 1000000
theorem Soundness (φ : Formula) : ⊢ φ → ⊨ φ := by
  intro mp
  have ⟨𝕏, x, prop⟩ := mp
  by_contra h
  simp [isValid] at h
  have ⟨W, M, u, u_prop⟩ := h
  let chain : (n : Nat) → (x : 𝕏.X) × {w : W // ¬ Evaluate_seq ⟨M, w⟩ (f (r 𝕏.α x))}
    := Nat.rec ⟨x, ⟨u, by simp_all⟩⟩ (fun n ⟨x_ih, w_ih, w_ih_prop⟩ =>
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
              have h : ¬Evaluate_seq (M, w_ih) (f (r 𝕏.α y)) := by sorry -- have to use \𝕏.h here to determine y is the child.
              ⟨y, w_ih, h⟩
            else
              have h : ¬Evaluate_seq (M, w_ih) (f (r 𝕏.α z)) := by sorry
              ⟨z, w_ih, h⟩
          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | [y] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::z::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .or Δ φ₁ φ₂ in_Δ => match p_def : p 𝕏.α x_ih with
          | [y] => by
            have := not_or.1 $ fun x ↦ (not_exists.1 w_ih_prop) (φ₁ v φ₂) ⟨(r_def ▸ in_Δ), x⟩
            have h : ¬Evaluate_seq (M, w_ih) (f (r 𝕏.α y)) := by sorry -- have to use \𝕏.h here to determine y is the child.
          --  have ⟨y, y_prop, x_y⟩ := or_premises r_def
          -- simp_all only [Evaluate_seq, not_exists, not_and]
          -- have := w_ih_prop (φ₁ v φ₂) in_Δ
          -- simp only [Evaluate, not_or] at this
          -- refine ⟨y, w_ih, ?_⟩
          -- simp only [y_prop, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
          -- intro ψ ψ_cases
          -- rcases ψ_cases with c | c
          -- · exact w_ih_prop ψ c.1
          -- · simp at c
          --   rcases c with c | c
          --   all_goals
          --     subst c
          --     simp [this]
            exact ⟨y, w_ih, h⟩

          | [] => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)
          | x::y::l => False.elim (by have := 𝕏.h x_ih; simp [r_def, p_def] at this)

        | .box Δ φ in_Δ => sorry -- OLD VERSION BELOW
        -- by
        --   have ⟨y, y_prop, x_y⟩ := box_premises r_def
        --   simp_all [Evaluate_seq, not_exists, not_and]
        --   have w_next := w_ih_prop (□ φ) in_Δ
        --   simp at w_next
        --   refine ⟨y, w_next.choose, ?_⟩
        --   simp [y_prop, D]
        --   intro ψ ψ_cases
        --   rcases ψ_cases with c | c | c
        --   · cases ψ <;> simp [Formula.isDiamond] at c
        --     case diamond χ =>
        --       have w_ih_app := w_ih_prop (◇ χ) c
        --       simp at w_ih_app
        --       have := w_ih_app _ w_next.choose_spec.1
        --       -- something with transitivity here
        --       sorry
        --   · have ⟨χ, ⟨χ_in_Δ, χ_neq⟩, χ_eq⟩ := c
        --     cases χ <;> simp [Formula.opUnDi] at χ_eq
        --     case diamond χ =>
        --       subst χ_eq
        --       have w_ih_app := w_ih_prop (◇ χ) χ_in_Δ
        --       simp at w_ih_app
        --       exact w_ih_app _ w_next.choose_spec.1
        --   · subst c
        --     exact w_next.choose_spec.2
    )

  have chain_prop : ∀ n, edge 𝕏.α (chain n).1 (chain (n + 1)).1 := sorry
  sorry
