/- GL interpolation, using everything so far! -/
import GL.Logic
import GL.Semantics
import GL.Completeness2
import GL.SplitCompleteness2
import GL.PartialInterpolation
import GL.Interpolants
import GL.PartialInterpolation
import GL.SplitSoundness

def isInterpolant (φ : Formula) (ψ : Formula) (χ : Formula) :=
  χ.vocab ⊆ φ.vocab ∩ ψ.vocab ∧ ⊨ (φ ↣ χ) ∧ ⊨ (χ ↣ ψ)

theorem Interpolation (φ ψ : Formula) : ⊨ (φ ↣ ψ) → ∃ χ, isInterpolant φ ψ χ := by
  intro φ_ψ
  have φ_ψ_sseq : ⊨ {Sum.inl (~φ), Sum.inr ψ} := by
    simp [SplitSequent.isValid, Evaluate_sseq]
    exact φ_ψ
  have ⟨𝕏, 𝕏_proves⟩ := Split.Completeness _ φ_ψ_sseq
  have ⟨𝕐, Fin_𝕐, y, y_prop⟩ := Split.finite_proof_of_proof 𝕏 _ 𝕏_proves
  have Fintype_Y := @Fintype.ofFinite _ Fin_𝕐 -- maybe change the Finiteness proof to prove Fintype
  refine ⟨Split.Interpolant 𝕐 (at (Split.encodeVar y)), ?_, ?_, ?_⟩
  · sorry
  · have hl : (@Split.InterpolantProofLeft 𝕐 _) ⊢ {Sum.inl (~φ), Sum.inr (Split.Interpolant 𝕐 (at (Split.encodeVar y)))} := by sorry -- this should be the main theorem of the Partial Interpolation section
    have φ_χ := SplitCut.Soundness _ ⟨_, hl⟩
    simp [SplitSequent.isValid, Evaluate_sseq] at φ_χ
    exact φ_χ
  · sorry
