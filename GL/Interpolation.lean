import GL.Logic
import GL.Semantics
import GL.Completeness2
import GL.SplitCompleteness2
import GL.PartialInterpolation
import GL.Interpolants
import GL.PartialInterpolation
import GL.SplitSoundness

/-! ## Interpolation

We use everything we have proven so far to show that GL has interpolation!
-/


/-- Definition of Craig interpolation for modal formulas. -/
def isInterpolant (φ : Formula) (ψ : Formula) (χ : Formula) :=
  χ.vocab ⊆ φ.vocab ∩ ψ.vocab ∧ ⊨ (φ ↣ χ) ∧ ⊨ (χ ↣ ψ)


/-- Sorry-free interpolation theorem! -/
theorem Interpolation (φ ψ : Formula) : ⊨ (φ ↣ ψ) → ∃ χ, isInterpolant φ ψ χ := by
  intro φ_ψ
  have φ_ψ_sseq : ⊨ {Sum.inl (~φ), Sum.inr ψ} := by
    simp [SplitSequent.isValid, evaluateSSeq]
    exact φ_ψ
  have ⟨𝕏, 𝕏_proves⟩ := Split.completeness_sseq _ φ_ψ_sseq
  have ⟨𝕐, fin_Y, y, y_prop⟩ := Split.finite_proof_of_proof 𝕏 _ 𝕏_proves
  have Fintype_Y := @Fintype.ofFinite _ fin_Y
  refine ⟨Split.Interpolant 𝕐 (at (Split.encodeVar y)), ?_, ?_, ?_⟩
  · have := (@Split.Interpolant_prop 𝕐 Fintype_Y y).2
    convert this
    · ext n
      simp [y_prop, SplitSequent.left, Sequent.vocab]
    · ext n
      simp [y_prop, SplitSequent.right, Sequent.vocab]
  · have hl := Split.InterpolantProofLeft_proves_interpolant y
    have φ_χ := SplitCut.soundness_sseq _ ⟨_, hl⟩
    simp [SplitSequent.isValid, evaluateSSeq, Split.leftInterpolantSequent, y_prop] at φ_χ
    simp [Formula.isValid]
    grind
  · have hr := Split.InterpolantProofRight_proves_interpolant y
    have φ_χ := SplitCut.soundness_sseq _ ⟨_, hr⟩
    simp [SplitSequent.isValid, evaluateSSeq, Split.rightInterpolantSequent, y_prop] at φ_χ
    simp [Formula.isValid]
    grind
