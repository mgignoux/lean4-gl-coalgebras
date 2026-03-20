import GL.Logic
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Interpolants
import GL.SplitCutCoalgebraProof
import GL.ProofTransformations

namespace Split

noncomputable def leftInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (at (encodeVar x)))} ∪ (SplitSequent.filterLeft (f (r 𝕏.α x)))

noncomputable def leftEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (equation x))} ∪ (SplitSequent.filterLeft (f (r 𝕏.α x)))

noncomputable def rightInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (Interpolant 𝕏 (at (encodeVar x))))} ∪ (SplitSequent.filterRight (f (r 𝕏.α x)))

noncomputable def rightEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (Interpolant 𝕏 (equation x)))} ∪ (SplitSequent.filterRight (f (r 𝕏.α x)))

def Split_to_CutPre {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : Split.RuleApp → CutPre.RuleApp x τ
  | .topₗ _ in_Δ => .topₗ _ in_Δ
  | .topᵣ _ in_Δ => .topᵣ _ in_Δ
  | .axₗₗ _ _ in_Δ => .axₗₗ _ _ in_Δ
  | .axₗᵣ _ _ in_Δ => .axₗᵣ _ _ in_Δ
  | .axᵣₗ _ _ in_Δ => .axᵣₗ _ _ in_Δ
  | .axᵣᵣ _ _ in_Δ => .axᵣᵣ _ _ in_Δ
  | .orₗ _ _ _ in_Δ => .orₗ _ _ _ in_Δ
  | .orᵣ _ _ _ in_Δ => .orᵣ _ _ _ in_Δ
  | .andₗ _ _ _ in_Δ => .andₗ _ _ _ in_Δ
  | .andᵣ _ _ _ in_Δ => .andᵣ _ _ _ in_Δ
  | .boxₗ _ _ in_Δ => .boxₗ _ _ in_Δ
  | .boxᵣ _ _ in_Δ => .boxᵣ _ _ in_Δ

lemma Split_to_CutPre_isBox {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : r.isBox → (@Split_to_CutPre _ x τ r).isBox := by
  unfold Split_to_CutPre
  cases r <;> simp [RuleApp.isBox, CutPre.RuleApp.isBox]

lemma Split_to_CutPre_notNonAxLeaf {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : ¬ (@Split_to_CutPre _ x τ r).isNonAxLeaf := by
  unfold Split_to_CutPre
  cases r <;> simp [CutPre.RuleApp.isNonAxLeaf]

theorem Split_to_CutPre_f {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : CutPre.f (@Split_to_CutPre _ x τ r) = f r := by
  unfold Split_to_CutPre
  cases r <;> simp [f, CutPre.f]

theorem Split_to_CutPre_fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : CutPre.fₚ (@Split_to_CutPre _ x τ r) = fₚ r := by
  unfold Split_to_CutPre
  cases r <;> simp [fₚ, CutPre.fₚ]

theorem Split_to_CutPre_fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : CutPre.fₙ (@Split_to_CutPre _ x τ r) = fₙ r := by
  unfold Split_to_CutPre
  cases r <;> simp [fₙ_alternate, CutPre.fₙ_alternate]

/-! # Partial Interpolation Proofs

All the left and right partial interpolation proofs, split apart based on rule application. These are
split apart since they run very slow otherwise. -/

noncomputable def PartialLeft_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.topₗ (leftEquationSequent x) (by simp [leftEquationSequent, rule_def, f]; exact in_Δ), {}⟩
    step u := by simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialLeft_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
   : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.topᵣ (leftEquationSequent x) (by
      simp [leftEquationSequent, equation, rule_def] -- why not able to simpe with rule here
      split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialLeft_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.axₗₗ (leftEquationSequent x) n (by simp [leftEquationSequent, rule_def, f, in_Δ]), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialLeft_axₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.axₗᵣ (leftEquationSequent x) n (by
      simp [leftEquationSequent, rule_def, f, in_Δ]
      simp [Interpolant, equation]
      split <;> simp_all
      apply partial_const
      simp [Formula.vocab]
      intro _ _
      apply at_in_not_encodeVar
      simp [Proof.Sequent]
      refine ⟨x, Fintype.complete x, Or.inl ?_⟩
      convert in_Δ.1
      simp_all [f]
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialLeft_axᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.axᵣₗ (leftEquationSequent x) n (by
      simp [leftEquationSequent, rule_def, f, in_Δ]
      simp [Interpolant, equation]
      split <;> simp_all
      apply partial_const
      simp [Formula.vocab]
      intro _ _
      apply at_in_not_encodeVar
      simp [Proof.Sequent]
      refine ⟨x, Fintype.complete x, Or.inr ?_⟩
      convert in_Δ.1
      simp_all [f]
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialLeft_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.topᵣ (leftEquationSequent x) (by
      simp [leftEquationSequent, rule_def, f, equation]
      split <;> simp_all [Interpolant, partial_]
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialLeft_orₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
: CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
          rw [equation]
          split <;> simp_all
        { X := Fin 2
          α | 0 => ⟨CutPre.RuleApp.orₗ (leftEquationSequent x) φ ψ (by simp [leftEquationSequent, rule_def, f, in_Δ]), [1]⟩
            | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
          step := by
            have 𝕏_h := 𝕏.step x
            simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
            intro n
            match n with
              | 0 =>
                simp [CutPre.r, CutPre.p, CutPre.T, CutPre.f, CutPre.fₙ, CutPre.fₚ, leftInterpolantSequent, leftEquationSequent, rule_def, 𝕏_h, interpolant_eq]
                aesop -- big aesop
              | 1 =>
                simp [CutPre.r, CutPre.p]
          root := 0
          path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
        | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
        | y :: z :: l => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialLeft_orᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
    | [y] =>
      have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
        rw [equation]
        split <;> simp_all
    { X := Unit
      α u := ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      step := by simp [CutPre.r, CutPre.p]
      root := ()
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
    | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
    | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

set_option maxHeartbeats 400000 in
noncomputable def PartialLeft_andₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) v Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    if eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z)
    then {
    X := Fin 4
    α | 0 => ⟨CutPre.RuleApp.orᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨CutPre.RuleApp.andₗ (((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {(Sum.inr $ Interpolant 𝕏 (at encodeVar y)), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))}) φ ψ (by simp [leftEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      | 3 => ⟨CutPre.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
      | 1 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, leftInterpolantSequent, 𝕏_h, eq]
        constructor <;> ext <;> simp [f] <;> aesop
      | 2 => by simp [CutPre.r, CutPre.p]
      | 3 => by simp [CutPre.r, CutPre.p]
    root := 0
    path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
    else {
    X := Fin 6
    α | 0 => ⟨CutPre.RuleApp.orᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨CutPre.RuleApp.andₗ (((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {(Sum.inr $ Interpolant 𝕏 (at encodeVar y)), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))}) φ ψ (by simp [leftEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨CutPre.RuleApp.wkᵣ ((((((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {Sum.inr $ Interpolant 𝕏 (at encodeVar y), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))})) \ {Sum.inl (φ & ψ)}) ∪ {Sum.inl φ}) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [4]⟩
      | 3 => ⟨CutPre.RuleApp.wkᵣ ((((((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {Sum.inr $ Interpolant 𝕏 (at encodeVar y), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))})) \ {Sum.inl (φ & ψ)}) ∪ {Sum.inl ψ}) (Interpolant 𝕏 (at encodeVar y)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [5]⟩
      | 4 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      | 5 => ⟨CutPre.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
      | 1 => by simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
      | 2 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
        ext; simp [f]; aesop
      | 3 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
        ext; simp [f]; aesop
      | 4 => by simp [CutPre.r, CutPre.p]
      | 5 => by simp [CutPre.r, CutPre.p]
    root := 0
    path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialLeft_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) & Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨CutPre.RuleApp.andᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1,2]⟩
        | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
        | 2 => ⟨CutPre.RuleApp.pre z (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
          constructor <;> ext <;> simp [f] <;> aesop
        | 1 => by simp [CutPre.r, CutPre.p]
        | 2 => by simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialLeft_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = ◇ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨CutPre.RuleApp.boxₗ (leftEquationSequent x) φ (by simp [leftEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨CutPre.RuleApp.wkᵣ (((leftEquationSequent x) \ {Sum.inl $ □ φ}).D ∪ {Sum.inl φ}) (◇ (Interpolant 𝕏 (at encodeVar y))) (by simp [leftEquationSequent, rule_def, f, interpolant_eq, SplitSequent.D, SplitFormula.isDiamond]), [2]⟩
        | 2 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
        | 1 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
          simp [SplitFormula.isDiamond]
          constructor <;> try tauto
          intro mp
          subst mp
          simp
          induction Interpolant 𝕏 (at encodeVar y) <;> simp_all
        | 2 => by simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialLeft_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = □ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 2
      α | 0 => ⟨CutPre.RuleApp.boxᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (by simp [leftEquationSequent, interpolant_eq]), [1]⟩
        | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [CutPre.r, CutPre.p, leftEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
        | 1 => by simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialInterpolationLeft_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match rule_def : (r 𝕏.α x) with
    | .topₗ _ _ => PartialLeft_topₗ x rule_def
    | .topᵣ _ _ => PartialLeft_topᵣ x rule_def
    | .axₗₗ _ _ _ => PartialLeft_axₗₗ x rule_def
    | .axₗᵣ _ _ _ => PartialLeft_axₗᵣ x rule_def
    | .axᵣₗ _ _ _ => PartialLeft_axᵣₗ x rule_def
    | .axᵣᵣ _ _ _ => PartialLeft_axᵣᵣ x rule_def
    | .orₗ _ _ _ _ => PartialLeft_orₗ x rule_def
    | .orᵣ _ _ _ _ => PartialLeft_orᵣ x rule_def
    | .andₗ _ _ _ _ => PartialLeft_andₗ x rule_def
    | .andᵣ _ _ _ _ => PartialLeft_andᵣ x rule_def
    | .boxₗ _ _ _ => PartialLeft_boxₗ x rule_def
    | .boxᵣ _ _ _ => PartialLeft_boxᵣ x rule_def

lemma PartialInterpolationLeft_eq_proves_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  CutPre.Proves x (PartialInterpolationLeft_eq x) (leftEquationSequent x) := by
    have 𝕏_h := 𝕏.step x
    unfold PartialInterpolationLeft_eq
    split <;> simp_all [CutPre.Proves, CutPre.r, List.map_eq_cons_iff]
    · simp [PartialLeft_topₗ, CutPre.f]
    · simp [PartialLeft_topᵣ, CutPre.f]
    · simp [PartialLeft_axₗₗ, CutPre.f]
    · simp [PartialLeft_axₗᵣ, CutPre.f]
    · simp [PartialLeft_axᵣₗ, CutPre.f]
    · simp [PartialLeft_axᵣᵣ, CutPre.f]
    · simp [PartialLeft_orₗ]
      split <;> simp_all [CutPre.f]
    · rename_i rule_def
      simp [PartialLeft_orᵣ]
      have ⟨y, p_def, prop⟩ := 𝕏_h
      split <;> simp_all [CutPre.f]
      simp [leftInterpolantSequent, leftEquationSequent, prop, rule_def]
      apply congrArg₂
      · simp [equation]; split <;> simp_all
      · simp [f, fₙ, fₚ]
        aesop
    · rename_i rule_def
      have ⟨y, z, p_def, prop⟩ := 𝕏_h
      simp [PartialLeft_andₗ]
      split <;> simp_all
      have ⟨eq₁, eq₂⟩ := p_def
      by_cases eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z) <;> subst eq₁ eq₂
      · rw [dif_pos eq]
        simp [CutPre.f]
      · rw [dif_neg eq]
        simp [CutPre.f]
    · simp [PartialLeft_andᵣ]
      split <;> simp_all [CutPre.f]
    · simp [PartialLeft_boxₗ]
      split <;> simp_all [CutPre.f]
    · simp [PartialLeft_boxᵣ]
      split <;> simp_all [CutPre.f]

set_option maxHeartbeats 1000000 in
noncomputable def PartialInterpolationLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
  then PartialInterpolationLeft_eq x
  else
    have equiv : Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x) := by
      have := (Interpolant_prop x ).1
      simp_all
    let 𝕐₁ := PartialInterpolationLeft_eq x
    let y₁ := 𝕐₁.root
    have y₁_prop := PartialInterpolationLeft_eq_proves_eq x
    let 𝕐₂ := equiv.1.choose
    let y₂ := equiv.1.choose_spec.choose
    have y₂_prop := equiv.1.choose_spec.choose_spec
    { X := Unit ⊕ 𝕐₁.X ⊕ 𝕐₂.X
      α | Sum.inl u => ⟨CutPre.RuleApp.cutᵣ (leftInterpolantSequent x) (Interpolant 𝕏 (equation x)), [Sum.inr (Sum.inl y₁), Sum.inr (Sum.inr y₂)]⟩
        | Sum.inr (Sum.inl z₁) => ⟨CutPre.r 𝕐₁.α z₁, List.map (Sum.inr ∘ Sum.inl) (CutPre.p 𝕐₁.α z₁)⟩
        | Sum.inr (Sum.inr z₂) => ⟨Split_to_CutPre (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩
      step
        | Sum.inl u => by
          simp only [CutPre.r, CutPre.T, CutPre.p, List.map_cons, Split_to_CutPre_f, List.map_nil, CutPre.fₙ_alternate, List.cons.injEq, and_true]
          constructor
          · convert y₁_prop
            simp [leftEquationSequent, leftInterpolantSequent]
            aesop
          · convert y₂_prop using 1
            simp [leftInterpolantSequent]
            aesop
        | Sum.inr (Sum.inl z₁) => by
          have 𝕐₁_h := 𝕐₁.step z₁
          convert 𝕐₁_h <;> simp [CutPre.p, CutPre.r]
        | Sum.inr (Sum.inr z₂) => by
          have 𝕐₂_h := 𝕐₂.step z₂
          split
          all_goals
            rename_i eq
            cases r_def : r 𝕐₂.α z₂ <;> simp [CutPre.r, r_def, Split_to_CutPre] at eq
            all_goals
              simp [r_def] at 𝕐₂_h
              simp [CutPre.p, 𝕐₂_h]
              all_goals
                convert 𝕐₂_h
                all_goals
                  try simp [r_def, CutPre.r, Split_to_CutPre_f, Split_to_CutPre_fₙ]
                  try tauto
      root := Sum.inl ()
      path | Sum.inl u, f => by
              have := f.2.2 0
              simp [CutPre.edge, CutPre.p, f.2.1] at this
              rcases this with f1_def | f1_def
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
                have isLeft : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isLeft := by
                  intro n
                  induction n
                  case zero => simp [f1_def]
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with _ | l | r
                    · have := isRight k
                      simp [fk_def] at this
                    · simp [CutPre.edge, CutPre.p, fk_def] at step
                      grind
                    · simp [fk_def] at ih
                let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 (n + 1)) (isRight n)) (isLeft n)
                have g_zero : g 0 = y₁ := by unfold g; simp [f1_def]
                have g_succ : ∀ n, CutPre.edge 𝕐₁.α (g n) (g (n + 1)) := by
                  intro n
                  have step := f.2.2 (n + 1)
                  rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
                  · have := isRight n
                    simp [fn_def] at this
                  · simp [CutPre.edge, CutPre.p, fn_def] at step
                    simp [CutPre.edge, CutPre.p]
                    grind
                  · have := isLeft n
                    simp [fn_def] at this
                intro n
                have ⟨m, m_prop⟩ := 𝕐₁.path y₁ ⟨g, g_zero, g_succ⟩ n
                use m + 1
                convert m_prop
                unfold g
                simp [CutPre.r]
                grind
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
                have isRight' : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isRight := by
                  intro n
                  induction n
                  case zero => simp [f1_def]
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with _ | l | r
                    · have := isRight k
                      simp [fk_def] at this
                    · simp [fk_def] at ih
                    · simp [CutPre.edge, CutPre.p, fk_def] at step
                      grind
                let g : ℕ → 𝕐₂.X := fun n ↦ Sum.getRight (Sum.getRight (f.1 (n + 1)) (isRight n)) (isRight' n)
                have g_zero : g 0 = y₂ := by unfold g; simp [f1_def]
                have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
                  intro n
                  have step := f.2.2 (n + 1)
                  rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
                  · have := isRight n
                    simp [fn_def] at this
                  · have := isRight' n
                    simp [fn_def] at this
                  · simp [CutPre.edge, CutPre.p, fn_def] at step
                    simp [edge]
                    grind
                intro n
                have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
                use m + 1
                simp [CutPre.r]
                rcases fn_def : f.1 (n + m + 1) with _ | _ | gn_def
                · have := isRight (n + m)
                  simp [fn_def] at this
                · have := isRight' (n + m)
                  simp [fn_def] at this
                · simp [←add_assoc, fn_def]
                  apply Split_to_CutPre_isBox
                  convert m_prop
                  unfold g
                  simp [fn_def]
           | Sum.inr (Sum.inl z), f => by
              have isRight : ∀ n, (f.1 n).isRight := by
                intro n
                induction n
                case zero => rw [f.2.1]; simp
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
                  simp [CutPre.edge, CutPre.p, fk_def] at step
                  grind
              have isLeft : ∀ n, ((f.1 n).getRight (isRight n)).isLeft := by
                intro n
                induction n
                case zero => simp [f.2.1]
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with _ | l | r
                  · have := isRight k
                    simp [fk_def] at this
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
                  · simp [fk_def] at ih
              let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 n) (isRight n)) (isLeft n)
              have g_zero : g 0 = z := by unfold g; simp [f.2.1]
              have g_succ : ∀ n, CutPre.edge 𝕐₁.α (g n) (g (n + 1)) := by
                intro n
                have step := f.2.2 n
                rcases fn_def : f.1 n with _ | _ | gn_def
                · have := isRight n
                  simp [fn_def] at this
                · simp [CutPre.edge, CutPre.p, fn_def] at step
                  simp [CutPre.edge, CutPre.p]
                  grind
                · have := isLeft n
                  simp [fn_def] at this
              intro n
              have ⟨m, m_prop⟩ := 𝕐₁.path z ⟨g, g_zero, g_succ⟩ n
              use m
              convert m_prop
              unfold g
              simp [CutPre.r]
              grind
           | Sum.inr (Sum.inr z), f => by
              have isRight : ∀ n, (f.1 n).isRight := by
                intro n
                induction n
                case zero => rw [f.2.1]; simp
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
                  simp [CutPre.edge, CutPre.p, fk_def] at step
                  grind
              have isRight' : ∀ n, ((f.1 n).getRight (isRight n)).isRight := by
                intro n
                induction n
                case zero => simp [f.2.1]
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with _ | l | r
                  · have := isRight k
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
              let g : ℕ → 𝕐₂.X := fun n ↦ Sum.getRight (Sum.getRight (f.1 n) (isRight n)) (isRight' n)
              have g_zero : g 0 = z := by unfold g; simp [f.2.1]
              have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
                intro n
                have step := f.2.2 n
                rcases fn_def : f.1 n with _ | _ | gn_def
                · have := isRight n
                  simp [fn_def] at this
                · have := isRight' n
                  simp [fn_def] at this
                · simp [CutPre.edge, CutPre.p, fn_def] at step
                  simp [edge]
                  grind
              intro n
              have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
              use m
              simp [CutPre.r]
              rcases fn_def : f.1 (n + m) with _ | _ | gn_def
              · have := isRight (n + m)
                simp [fn_def] at this
              · have := isRight' (n + m)
                simp [fn_def] at this
              · apply Split_to_CutPre_isBox
                convert m_prop
                unfold g
                simp [fn_def]}

lemma PartialInterpolationLeft_proves_int {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  CutPre.Proves x (PartialInterpolationLeft x) (leftInterpolantSequent x) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then (by
    convert PartialInterpolationLeft_eq_proves_eq x using 1
    · unfold PartialInterpolationLeft
      simp [eq]
    · unfold leftInterpolantSequent leftEquationSequent
      simp [eq])
  else by
    unfold PartialInterpolationLeft
    simp [eq]
    simp [CutPre.Proves, CutPre.r, CutPre.f]

open Classical in
set_option maxHeartbeats 300000 in
theorem PartialInterpolationLeft_box_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  (r 𝕏.α x).isBox →
    ∀ (n : ℕ) (f : Fin (n + 1) → (PartialInterpolationLeft x).X),
      f 0 = (PartialInterpolationLeft x).root →
        (CutPre.r (PartialInterpolationLeft x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
          (∀ (m : Fin n), CutPre.edge (PartialInterpolationLeft x).α (f m.castSucc) (f m.succ)) →
            ∃ m, (CutPre.r (PartialInterpolationLeft x).α (f m)).isBox := by
  intro is_box n-- f f_zero f_last f_succ
  have 𝕏_h := 𝕏.step x
  cases r_def : r 𝕏.α x <;> simp_all [RuleApp.isBox]
  case boxₗ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold PartialInterpolationLeft
      rw [dif_pos eq, PartialInterpolationLeft_eq]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [PartialLeft_boxₗ, f_zero]
      split <;> simp_all
      simp [CutPre.r, CutPre.RuleApp.isBox]
    · unfold PartialInterpolationLeft
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [CutPre.r, CutPre.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, CutPre.edge, CutPre.p] at step
        rcases step with l | r
        · rw [l]
          simp [CutPre.r]
          simp [PartialInterpolationLeft_eq, PartialLeft_boxₗ]
          split <;> simp_all
          split <;> simp_all [CutPre.RuleApp.isBox]
        · exfalso
          simp [CutPre.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [CutPre.edge, CutPre.p, fk_def] at step
                grind
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_CutPre_notNonAxLeaf 𝕏 x leftInterpolantSequent _ f_last
  case boxᵣ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold PartialInterpolationLeft
      rw [dif_pos eq, PartialInterpolationLeft_eq]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [PartialLeft_boxᵣ, f_zero]
      split <;> simp_all
      simp [CutPre.r, CutPre.RuleApp.isBox]
    · unfold PartialInterpolationLeft
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [CutPre.r, CutPre.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, CutPre.edge, CutPre.p] at step
        rcases step with l | r
        · rw [l]
          simp [CutPre.r]
          simp [PartialInterpolationLeft_eq, PartialLeft_boxᵣ]
          split <;> simp_all
          split <;> simp_all [CutPre.RuleApp.isBox]
        · exfalso
          simp [CutPre.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [CutPre.edge, CutPre.p, fk_def] at step
                grind
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_CutPre_notNonAxLeaf 𝕏 x leftInterpolantSequent _ f_last

noncomputable def InterpolantProofLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : SplitCut.Proof :=
  @ProofTranslation 𝕏 (@leftInterpolantSequent 𝕏 _) PartialInterpolationLeft PartialInterpolationLeft_proves_int PartialInterpolationLeft_box_prop

theorem InterpolantProofLeft_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
  : @InterpolantProofLeft 𝕏 fin_X ⊢ leftInterpolantSequent x := by
  use ⟨x, (PartialInterpolationLeft x).root⟩
  unfold InterpolantProofLeft ProofTranslation
  simp [ProofTranslation_f]
  exact PartialInterpolationLeft_proves_int x



--------------------- RIGHT -------------- findme


/- PARTIAL INTERPOLANT PROOFS. I SPLIT THESE APART BECAUSE THEY RUN SO SLOW OTHERWISE -/
noncomputable def PartialRight_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
   : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.topₗ (rightEquationSequent x) (by
      simp [rightEquationSequent, equation, rule_def] -- why not able to simpe with rule here
      split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialRight_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) where
      X := Unit
      α u := ⟨CutPre.RuleApp.topᵣ (rightEquationSequent x) (by simp [rightEquationSequent, rule_def, f]; exact in_Δ), {}⟩
      step u := by simp [CutPre.r, CutPre.p]
      root := ()
      path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialRight_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.topₗ (rightEquationSequent x) (by simp [rightEquationSequent, rule_def, f]; simp [equation]; split <;> simp_all [Interpolant, partial_]), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialRight_axₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.axₗᵣ (rightEquationSequent x) n (by
      simp [rightEquationSequent, rule_def, f, in_Δ]
      simp [Interpolant, equation]
      split <;> simp_all
      rw [←partial_const] <;> simp
      simp [Formula.vocab]
      intro _ _
      apply at_in_not_encodeVar
      simp [Proof.Sequent]
      refine ⟨x, Fintype.complete x, Or.inl ?_⟩
      convert in_Δ.1
      simp_all [f]
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialRight_axᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.axᵣₗ (rightEquationSequent x) n (by
      simp [rightEquationSequent, rule_def, f, in_Δ]
      simp [Interpolant, equation]
      split <;> simp_all
      rw [←partial_const] <;> simp
      simp [Formula.vocab]
      intro _ _
      apply at_in_not_encodeVar
      simp [Proof.Sequent]
      refine ⟨x, Fintype.complete x, Or.inr ?_⟩
      convert in_Δ.1
      simp_all [f]
      ), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialRight_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨CutPre.RuleApp.axᵣᵣ (rightEquationSequent x) n (by simp [rightEquationSequent, rule_def, f, in_Δ]), {}⟩
    step := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    path u f := by exfalso; simp [CutPre.edge, CutPre.p] at f; exact f.2

noncomputable def PartialRight_orₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
: CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
          rw [equation]
          split <;> simp_all
        { X := Unit
          α u := ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
          step := by simp [CutPre.r, CutPre.p]
          root := ()
          path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
        | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
        | y :: z :: l => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialRight_orᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
    | [y] =>
      have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
        rw [equation]
        split <;> simp_all
    { X := Fin 2
      α | 0 => ⟨CutPre.RuleApp.orᵣ (rightEquationSequent x) φ ψ (by simp [rightEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      step := by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        intro n
        match n with
          | 0 =>
            simp [CutPre.r, CutPre.p, CutPre.T, CutPre.f, CutPre.fₙ, CutPre.fₚ, rightInterpolantSequent, rightEquationSequent, rule_def, 𝕏_h, interpolant_eq]
            aesop -- big aesop
          | 1 =>
            simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
    | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
    | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialRight_andₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) v Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨CutPre.RuleApp.andₗ (rightEquationSequent x) (~ (Interpolant 𝕏 (at encodeVar y))) (~ (Interpolant 𝕏 (at encodeVar z))) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1,2]⟩
        | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
        | 2 => ⟨CutPre.RuleApp.pre z (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
          constructor <;> ext <;> simp [f] <;> aesop
        | 1 => by simp [CutPre.r, CutPre.p]
        | 2 => by simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

set_option maxHeartbeats 400000 in
noncomputable def PartialRight_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) & Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    if eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z)
    then {
    X := Fin 4
    α | 0 => ⟨CutPre.RuleApp.orₗ (rightEquationSequent x) (~Interpolant 𝕏 (at encodeVar y)) (~Interpolant 𝕏 (at encodeVar z)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨CutPre.RuleApp.andᵣ (((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {(Sum.inl $ ~Interpolant 𝕏 (at encodeVar y)), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)}) φ ψ (by simp [rightEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      | 3 => ⟨CutPre.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
      | 1 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, rightInterpolantSequent, 𝕏_h, eq]
        constructor <;> ext <;> simp [f] <;> aesop
      | 2 => by simp [CutPre.r, CutPre.p]
      | 3 => by simp [CutPre.r, CutPre.p]
    root := 0
    path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
    else {
    X := Fin 6
    α | 0 => ⟨CutPre.RuleApp.orₗ (rightEquationSequent x) (~Interpolant 𝕏 (at encodeVar y)) (~Interpolant 𝕏 (at encodeVar z)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨CutPre.RuleApp.andᵣ (((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {(Sum.inl $ ~Interpolant 𝕏 (at encodeVar y)), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)}) φ ψ (by simp [rightEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨CutPre.RuleApp.wkₗ ((((((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {Sum.inl $ ~Interpolant 𝕏 (at encodeVar y), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)})) \ {Sum.inr (φ & ψ)}) ∪ {Sum.inr φ}) (~Interpolant 𝕏 (at encodeVar z)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [4]⟩
      | 3 => ⟨CutPre.RuleApp.wkₗ ((((((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {Sum.inl $ ~Interpolant 𝕏 (at encodeVar y), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)})) \ {Sum.inr (φ & ψ)}) ∪ {Sum.inr ψ}) (~Interpolant 𝕏 (at encodeVar y)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [5]⟩
      | 4 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      | 5 => ⟨CutPre.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
      | 1 => by simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
      | 2 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
        ext ψ
        rcases ψ with ψ | ψ <;> simp [f]
        constructor <;> try tauto
        intro mp; subst mp; simp_all
        intro con; apply eq; apply Formula.neg_eq; exact con
      | 3 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
        ext ψ
        rcases ψ with ψ | ψ <;> simp [f]
        constructor <;> try tauto
        intro mp; subst mp; simp_all
        intro con; apply eq; apply Formula.neg_eq; exact Eq.symm con
      | 4 => by simp [CutPre.r, CutPre.p]
      | 5 => by simp [CutPre.r, CutPre.p]
    root := 0
    path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialRight_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = ◇ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 2
      α | 0 => ⟨CutPre.RuleApp.boxₗ (rightEquationSequent x) (~(Interpolant 𝕏 (at encodeVar y))) (by simp [rightEquationSequent, interpolant_eq]), [1]⟩
        | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
        | 1 => by simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialRight_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = □ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨CutPre.RuleApp.boxᵣ (rightEquationSequent x) φ (by simp [rightEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨CutPre.RuleApp.wkₗ (((rightEquationSequent x) \ {Sum.inr $ □ φ}).D ∪ {Sum.inr φ}) (◇ (~(Interpolant 𝕏 (at encodeVar y)))) (by simp [rightEquationSequent, rule_def, f, interpolant_eq, SplitSequent.D, SplitFormula.isDiamond]), [2]⟩
        | 2 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, f, interpolant_eq, CutPre.f, CutPre.fₙ_alternate]
        | 1 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [CutPre.r, CutPre.p, rightEquationSequent, rule_def, interpolant_eq, CutPre.f, CutPre.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
          simp [SplitFormula.isDiamond]
          constructor <;> try tauto
          intro mp
          subst mp
          simp
          induction Interpolant 𝕏 (at encodeVar y) <;> simp_all -- MALVIN so weird
        | 2 => by simp [CutPre.r, CutPre.p]
      root := 0
      path z f := by exfalso; simp [CutPre.edge, CutPre.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def PartialInterpolationRight_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  match rule_def : (r 𝕏.α x) with
    | .topₗ _ _ => PartialRight_topₗ x rule_def
    | .topᵣ _ _ => PartialRight_topᵣ x rule_def
    | .axₗₗ _ _ _ => PartialRight_axₗₗ x rule_def
    | .axₗᵣ _ _ _ => PartialRight_axₗᵣ x rule_def
    | .axᵣₗ _ _ _ => PartialRight_axᵣₗ x rule_def
    | .axᵣᵣ _ _ _ => PartialRight_axᵣᵣ x rule_def
    | .orₗ _ _ _ _ => PartialRight_orₗ x rule_def
    | .orᵣ _ _ _ _ => PartialRight_orᵣ x rule_def
    | .andₗ _ _ _ _ => PartialRight_andₗ x rule_def
    | .andᵣ _ _ _ _ => PartialRight_andᵣ x rule_def
    | .boxₗ _ _ _ => PartialRight_boxₗ x rule_def
    | .boxᵣ _ _ _ => PartialRight_boxᵣ x rule_def

lemma PartialInterpolationRight_eq_proves_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  CutPre.Proves x (PartialInterpolationRight_eq x) (rightEquationSequent x) := by
    have 𝕏_h := 𝕏.step x
    unfold PartialInterpolationRight_eq
    split <;> simp_all [CutPre.Proves, CutPre.r, List.map_eq_cons_iff]
    · simp [PartialRight_topₗ, CutPre.f]
    · simp [PartialRight_topᵣ, CutPre.f]
    · simp [PartialRight_axₗₗ, CutPre.f]
    · simp [PartialRight_axₗᵣ, CutPre.f]
    · simp [PartialRight_axᵣₗ, CutPre.f]
    · simp [PartialRight_axᵣᵣ, CutPre.f]
    · rename_i rule_def
      simp [PartialRight_orₗ]
      have ⟨y, p_def, prop⟩ := 𝕏_h
      split <;> simp_all [CutPre.f]
      simp [rightInterpolantSequent, rightEquationSequent, prop, rule_def]
      apply congrArg₂
      · simp [equation]; split <;> simp_all
      · simp [f, fₙ, fₚ]
        aesop
    · simp [PartialRight_orᵣ]
      split <;> simp_all [CutPre.f]
    · simp [PartialRight_andₗ]
      split <;> simp_all [CutPre.f]
    · rename_i rule_def
      have ⟨y, z, p_def, prop⟩ := 𝕏_h
      simp [PartialRight_andᵣ]
      split <;> simp_all
      have ⟨eq₁, eq₂⟩ := p_def
      by_cases eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z) <;> subst eq₁ eq₂
      · rw [dif_pos eq]
        simp [CutPre.f]
      · rw [dif_neg eq]
        simp [CutPre.f]
    · simp [PartialRight_boxₗ]
      split <;> simp_all [CutPre.f]
    · simp [PartialRight_boxᵣ]
      split <;> simp_all [CutPre.f]

set_option maxHeartbeats 1000000 in
noncomputable def PartialInterpolationRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises x (@rightInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
  then PartialInterpolationRight_eq x
  else
    have equiv : Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x) := by
      have := (Interpolant_prop x).1
      simp_all
    let 𝕐₁ := PartialInterpolationRight_eq x
    let y₁ := 𝕐₁.root
    have y₁_prop := PartialInterpolationRight_eq_proves_eq x
    let 𝕐₂ := equiv.2.choose
    let y₂ := equiv.2.choose_spec.choose
    have y₂_prop := equiv.2.choose_spec.choose_spec
    { X := Unit ⊕ 𝕐₁.X ⊕ 𝕐₂.X
      α | Sum.inl u => ⟨CutPre.RuleApp.cutₗ (rightInterpolantSequent x) (~Interpolant 𝕏 (equation x)), [Sum.inr (Sum.inl y₁), Sum.inr (Sum.inr y₂)]⟩
        | Sum.inr (Sum.inl z₁) => ⟨CutPre.r 𝕐₁.α z₁, List.map (Sum.inr ∘ Sum.inl) (CutPre.p 𝕐₁.α z₁)⟩
        | Sum.inr (Sum.inr z₂) => ⟨Split_to_CutPre (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩
      step
        | Sum.inl u => by
          simp only [CutPre.r, CutPre.T, CutPre.p, List.map_cons, Split_to_CutPre_f, List.map_nil, CutPre.fₙ_alternate, List.cons.injEq, and_true]
          constructor
          · convert y₁_prop
            simp [rightEquationSequent, rightInterpolantSequent]
            aesop
          · convert y₂_prop using 1
            simp [rightInterpolantSequent]
            aesop
        | Sum.inr (Sum.inl z₁) => by
          have 𝕐₁_h := 𝕐₁.step z₁
          convert 𝕐₁_h <;> simp [CutPre.p, CutPre.r]
        | Sum.inr (Sum.inr z₂) => by
          have 𝕐₂_h := 𝕐₂.step z₂
          split
          all_goals
            rename_i eq
            cases r_def : r 𝕐₂.α z₂ <;> simp [CutPre.r, r_def, Split_to_CutPre] at eq
            all_goals
              simp [r_def] at 𝕐₂_h
              simp [CutPre.p, 𝕐₂_h]
              all_goals
                convert 𝕐₂_h
                all_goals
                  try simp [r_def, CutPre.r, Split_to_CutPre_f, Split_to_CutPre_fₙ]
                  try tauto
      root := Sum.inl ()
      path | Sum.inl u, f => by
              have := f.2.2 0
              simp [CutPre.edge, CutPre.p, f.2.1] at this
              rcases this with f1_def | f1_def
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
                have isLeft : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isLeft := by
                  intro n
                  induction n
                  case zero => simp [f1_def]
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with _ | l | r
                    · have := isRight k
                      simp [fk_def] at this
                    · simp [CutPre.edge, CutPre.p, fk_def] at step
                      grind
                    · simp [fk_def] at ih
                let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 (n + 1)) (isRight n)) (isLeft n)
                have g_zero : g 0 = y₁ := by unfold g; simp [f1_def]
                have g_succ : ∀ n, CutPre.edge 𝕐₁.α (g n) (g (n + 1)) := by
                  intro n
                  have step := f.2.2 (n + 1)
                  rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
                  · have := isRight n
                    simp [fn_def] at this
                  · simp [CutPre.edge, CutPre.p, fn_def] at step
                    simp [CutPre.edge, CutPre.p]
                    grind
                  · have := isLeft n
                    simp [fn_def] at this
                intro n
                have ⟨m, m_prop⟩ := 𝕐₁.path y₁ ⟨g, g_zero, g_succ⟩ n
                use m + 1
                convert m_prop
                unfold g
                simp [CutPre.r]
                grind
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
                have isRight' : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isRight := by
                  intro n
                  induction n
                  case zero => simp [f1_def]
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with _ | l | r
                    · have := isRight k
                      simp [fk_def] at this
                    · simp [fk_def] at ih
                    · simp [CutPre.edge, CutPre.p, fk_def] at step
                      grind
                let g : ℕ → 𝕐₂.X := fun n ↦ Sum.getRight (Sum.getRight (f.1 (n + 1)) (isRight n)) (isRight' n)
                have g_zero : g 0 = y₂ := by unfold g; simp [f1_def]
                have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
                  intro n
                  have step := f.2.2 (n + 1)
                  rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
                  · have := isRight n
                    simp [fn_def] at this
                  · have := isRight' n
                    simp [fn_def] at this
                  · simp [CutPre.edge, CutPre.p, fn_def] at step
                    simp [edge]
                    grind
                intro n
                have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
                use m + 1
                simp [CutPre.r]
                rcases fn_def : f.1 (n + m + 1) with _ | _ | gn_def
                · have := isRight (n + m)
                  simp [fn_def] at this
                · have := isRight' (n + m)
                  simp [fn_def] at this
                · simp [←add_assoc, fn_def]
                  apply Split_to_CutPre_isBox
                  convert m_prop
                  unfold g
                  simp [fn_def]
           | Sum.inr (Sum.inl z), f => by
              have isRight : ∀ n, (f.1 n).isRight := by
                intro n
                induction n
                case zero => rw [f.2.1]; simp
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
                  simp [CutPre.edge, CutPre.p, fk_def] at step
                  grind
              have isLeft : ∀ n, ((f.1 n).getRight (isRight n)).isLeft := by
                intro n
                induction n
                case zero => simp [f.2.1]
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with _ | l | r
                  · have := isRight k
                    simp [fk_def] at this
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
                  · simp [fk_def] at ih
              let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 n) (isRight n)) (isLeft n)
              have g_zero : g 0 = z := by unfold g; simp [f.2.1]
              have g_succ : ∀ n, CutPre.edge 𝕐₁.α (g n) (g (n + 1)) := by
                intro n
                have step := f.2.2 n
                rcases fn_def : f.1 n with _ | _ | gn_def
                · have := isRight n
                  simp [fn_def] at this
                · simp [CutPre.edge, CutPre.p, fn_def] at step
                  simp [CutPre.edge, CutPre.p]
                  grind
                · have := isLeft n
                  simp [fn_def] at this
              intro n
              have ⟨m, m_prop⟩ := 𝕐₁.path z ⟨g, g_zero, g_succ⟩ n
              use m
              convert m_prop
              unfold g
              simp [CutPre.r]
              grind
           | Sum.inr (Sum.inr z), f => by
              have isRight : ∀ n, (f.1 n).isRight := by
                intro n
                induction n
                case zero => rw [f.2.1]; simp
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
                  simp [CutPre.edge, CutPre.p, fk_def] at step
                  grind
              have isRight' : ∀ n, ((f.1 n).getRight (isRight n)).isRight := by
                intro n
                induction n
                case zero => simp [f.2.1]
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with _ | l | r
                  · have := isRight k
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
              let g : ℕ → 𝕐₂.X := fun n ↦ Sum.getRight (Sum.getRight (f.1 n) (isRight n)) (isRight' n)
              have g_zero : g 0 = z := by unfold g; simp [f.2.1]
              have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
                intro n
                have step := f.2.2 n
                rcases fn_def : f.1 n with _ | _ | gn_def
                · have := isRight n
                  simp [fn_def] at this
                · have := isRight' n
                  simp [fn_def] at this
                · simp [CutPre.edge, CutPre.p, fn_def] at step
                  simp [edge]
                  grind
              intro n
              have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
              use m
              simp [CutPre.r]
              rcases fn_def : f.1 (n + m) with _ | _ | gn_def
              · have := isRight (n + m)
                simp [fn_def] at this
              · have := isRight' (n + m)
                simp [fn_def] at this
              · apply Split_to_CutPre_isBox
                convert m_prop
                unfold g
                simp [fn_def]}

lemma PartialInterpolationRight_proves_int {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  CutPre.Proves x (PartialInterpolationRight x) (rightInterpolantSequent x) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then (by
    convert PartialInterpolationRight_eq_proves_eq x using 1
    · unfold PartialInterpolationRight
      simp [eq]
    · unfold rightInterpolantSequent rightEquationSequent
      simp [eq])
  else by
    unfold PartialInterpolationRight
    simp [eq]
    simp [CutPre.Proves, CutPre.r, CutPre.f]

open Classical in
set_option maxHeartbeats 300000 in
theorem PartialInterpolationRight_box_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  (r 𝕏.α x).isBox →
    ∀ (n : ℕ) (f : Fin (n + 1) → (PartialInterpolationRight x).X),
      f 0 = (PartialInterpolationRight x).root →
        (CutPre.r (PartialInterpolationRight x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
          (∀ (m : Fin n), CutPre.edge (PartialInterpolationRight x).α (f m.castSucc) (f m.succ)) →
            ∃ m, (CutPre.r (PartialInterpolationRight x).α (f m)).isBox := by
  intro is_box n
  have 𝕏_h := 𝕏.step x
  cases r_def : r 𝕏.α x <;> simp_all [RuleApp.isBox]
  case boxₗ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold PartialInterpolationRight
      rw [dif_pos eq, PartialInterpolationRight_eq]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [PartialRight_boxₗ, f_zero]
      split <;> simp_all
      simp [CutPre.r, CutPre.RuleApp.isBox]
    · unfold PartialInterpolationRight
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [CutPre.r, CutPre.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, CutPre.edge, CutPre.p] at step
        rcases step with l | r
        · rw [l]
          simp [CutPre.r]
          simp [PartialInterpolationRight_eq, PartialRight_boxₗ]
          split <;> simp_all
          split <;> simp_all [CutPre.RuleApp.isBox]
        · exfalso
          simp [CutPre.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [CutPre.edge, CutPre.p, fk_def] at step
                grind
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_CutPre_notNonAxLeaf 𝕏 x rightInterpolantSequent _ f_last
  case boxᵣ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold PartialInterpolationRight
      rw [dif_pos eq, PartialInterpolationRight_eq]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [PartialRight_boxᵣ, f_zero]
      split <;> simp_all
      simp [CutPre.r, CutPre.RuleApp.isBox]
    · unfold PartialInterpolationRight
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [CutPre.r, CutPre.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, CutPre.edge, CutPre.p] at step
        rcases step with l | r
        · rw [l]
          simp [CutPre.r]
          simp [PartialInterpolationRight_eq, PartialRight_boxᵣ]
          split <;> simp_all
          split <;> simp_all [CutPre.RuleApp.isBox]
        · exfalso
          simp [CutPre.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [CutPre.edge, CutPre.p, fk_def] at step
                grind
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · simp [CutPre.edge, CutPre.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_CutPre_notNonAxLeaf 𝕏 x rightInterpolantSequent _ f_last

noncomputable def InterpolantProofRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : SplitCut.Proof :=
  @ProofTranslation 𝕏 (@rightInterpolantSequent 𝕏 _) PartialInterpolationRight PartialInterpolationRight_proves_int PartialInterpolationRight_box_prop

theorem InterpolantProofRight_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
  : @InterpolantProofRight 𝕏 fin_X ⊢ rightInterpolantSequent x := by
  use ⟨x, (PartialInterpolationRight x).root⟩
  unfold InterpolantProofRight ProofTranslation
  simp [ProofTranslation_f]
  exact PartialInterpolationRight_proves_int x
