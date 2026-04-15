import Mathlib.Data.Fintype.Defs
import GL.Interpolation.Interpolants
import GL.Split.ProofTransformations


open Split
/-- Given a node `x`, defines what the root of the left interpolation proof should look like,
    i.e. `f(x)ˡ ∣ ιₓ` in on paper work. -/
noncomputable def leftInterpolantSequent {𝕏 : Split.Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (at (encodeVar x)))} ∪ (SplitSequent.filterLeft (f (r 𝕏.α x)))

/-- Given a node `x`, defines what the same as above except for the equation `σ(χₓ)`, helpful for
    cases where the interpolant isn't defined by the interpolants of its premise nodes.,
    i.e. `f(x)ˡ ∣ σ(χₓ)` in on paper work. -/
noncomputable def leftEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (equation x))} ∪ (SplitSequent.filterLeft (f (r 𝕏.α x)))

/-- Given a node `x`, defines what the root of the right interpolation proof should look like,
    i.e. `~ιₓ ∣ f(x)ʳ ` in on paper work. -/
noncomputable def rightInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (Interpolant 𝕏 (at (encodeVar x))))} ∪ (SplitSequent.filterRight (f (r 𝕏.α x)))

/-- Given a node `x`, defines what the same as above except for the equation `σ(χₓ)`, helpful for
    cases where the interpolant isn't defined by the interpolants of its premise nodes.,
    i.e. `~σ(χₓ) ∣ f(x)ʳ ` in on paper work. -/
noncomputable def rightEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (Interpolant 𝕏 (equation x)))} ∪ (SplitSequent.filterRight (f (r 𝕏.α x)))

/- ## From split system to extended system -/
/-- Transforms rule applications in the split system into applications in the extended system. -/
def Split_to_Ext {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : Split.RuleApp → Ext.RuleApp x τ
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

lemma Split_to_Ext_isBox {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : r.isBox → (@Split_to_Ext _ x τ r).isBox := by
  unfold Split_to_Ext
  cases r <;> simp [RuleApp.isBox, Ext.RuleApp.isBox]

lemma Split_to_Ext_notNonAxLeaf {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : ¬ (@Split_to_Ext _ x τ r).isNonAxLeaf := by
  unfold Split_to_Ext
  cases r <;> simp [Ext.RuleApp.isNonAxLeaf]

lemma Split_to_Ext_f {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : Ext.f (@Split_to_Ext _ x τ r) = f r := by
  unfold Split_to_Ext
  cases r <;> simp [f, Ext.f]

lemma Split_to_Ext_fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : Ext.fₚ (@Split_to_Ext _ x τ r) = fₚ r := by
  unfold Split_to_Ext
  cases r <;> simp [fₚ, Ext.fₚ]

lemma Split_to_Ext_fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : Ext.fₙ (@Split_to_Ext _ x τ r) = fₙ r := by
  unfold Split_to_Ext
  cases r <;> simp [fₙ_alternate, Ext.fₙ_alternate]

/-! # Partial Left Interpolation Proofs

All of the left and right partial interpolation proofs, split apart based on rule application. These
are split apart since otherwise the file runs very slow. -/

noncomputable def partialLeft_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topₗ (leftEquationSequent x) (by simp [leftEquationSequent, rule_def, f]; exact in_Δ), {}⟩
    step u := by simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialLeft_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
   : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topᵣ (leftEquationSequent x) (by
      simp [leftEquationSequent, equation, rule_def] -- why not able to simp with rule here
      split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialLeft_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axₗₗ (leftEquationSequent x) n (by simp [leftEquationSequent, rule_def, f, in_Δ]), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialLeft_axₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axₗᵣ (leftEquationSequent x) n (by
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
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialLeft_axᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axᵣₗ (leftEquationSequent x) n (by
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
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialLeft_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topᵣ (leftEquationSequent x) (by
      simp [leftEquationSequent, rule_def, f, equation]
      split <;> simp_all [Interpolant, partial_]
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialLeft_orₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
: Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
          rw [equation]
          split <;> simp_all
        { X := Fin 2
          α | 0 => ⟨Ext.RuleApp.orₗ (leftEquationSequent x) φ ψ (by simp [leftEquationSequent, rule_def, f, in_Δ]), [1]⟩
            | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
          step := by
            have 𝕏_h := 𝕏.step x
            simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
            intro n
            match n with
              | 0 =>
                simp [Ext.r, Ext.p, Ext.T, Ext.f, Ext.fₙ, Ext.fₚ, leftInterpolantSequent, leftEquationSequent, rule_def, 𝕏_h, interpolant_eq]
                aesop -- big aesop
              | 1 =>
                simp [Ext.r, Ext.p]
          root := 0
          path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
        | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
        | y :: z :: l => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialLeft_orᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
    | [y] =>
      have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
        rw [equation]
        split <;> simp_all
    { X := Unit
      α u := ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step := by simp [Ext.r, Ext.p]
      root := ()
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
    | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

set_option maxHeartbeats 400000 in
noncomputable def partialLeft_andₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) v Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    if eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z)
    then {
    X := Fin 4
    α | 0 => ⟨Ext.RuleApp.orᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨Ext.RuleApp.andₗ (((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {(Sum.inr $ Interpolant 𝕏 (at encodeVar y)), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))}) φ ψ (by simp [leftEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 3 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
      | 1 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [Ext.r, Ext.p, leftEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, leftInterpolantSequent, 𝕏_h, eq]
        constructor <;> ext <;> simp [f] <;> aesop
      | 2 => by simp [Ext.r, Ext.p]
      | 3 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    else {
    X := Fin 6
    α | 0 => ⟨Ext.RuleApp.orᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨Ext.RuleApp.andₗ (((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {(Sum.inr $ Interpolant 𝕏 (at encodeVar y)), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))}) φ ψ (by simp [leftEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨Ext.RuleApp.wkᵣ ((((((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {Sum.inr $ Interpolant 𝕏 (at encodeVar y), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))})) \ {Sum.inl (φ & ψ)}) ∪ {Sum.inl φ}) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [4]⟩
      | 3 => ⟨Ext.RuleApp.wkᵣ ((((((leftEquationSequent x) \ {Sum.inr $ Interpolant 𝕏 (equation x)}) ∪ {Sum.inr $ Interpolant 𝕏 (at encodeVar y), Sum.inr $ (Interpolant 𝕏 (at encodeVar z))})) \ {Sum.inl (φ & ψ)}) ∪ {Sum.inl ψ}) (Interpolant 𝕏 (at encodeVar y)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [5]⟩
      | 4 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 5 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
      | 1 => by simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
      | 2 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [Ext.r, Ext.p, leftEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
        ext; simp [f]; aesop
      | 3 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [Ext.r, Ext.p, leftEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
        ext; simp [f]; aesop
      | 4 => by simp [Ext.r, Ext.p]
      | 5 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialLeft_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) & Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨Ext.RuleApp.andᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar z)) (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1,2]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
        | 2 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [Ext.r, Ext.p, leftEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
          constructor <;> ext <;> simp [f] <;> aesop
        | 1 => by simp [Ext.r, Ext.p]
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialLeft_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = ◇ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨Ext.RuleApp.boxₗ (leftEquationSequent x) φ (by simp [leftEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨Ext.RuleApp.wkᵣ (((leftEquationSequent x) \ {Sum.inl $ □ φ}).D ∪ {Sum.inl φ}) (◇ (Interpolant 𝕏 (at encodeVar y))) (by simp [leftEquationSequent, rule_def, f, interpolant_eq, SplitSequent.D, SplitFormula.isDiamond]), [2]⟩
        | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
        | 1 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [Ext.r, Ext.p, leftEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
          simp [SplitFormula.isDiamond]
          constructor <;> try tauto
          intro mp
          subst mp
          simp
          induction Interpolant 𝕏 (at encodeVar y) <;> simp_all
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialLeft_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = □ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 2
      α | 0 => ⟨Ext.RuleApp.boxᵣ (leftEquationSequent x) (Interpolant 𝕏 (at encodeVar y)) (by simp [leftEquationSequent, interpolant_eq]), [1]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [Ext.r, Ext.p, leftEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, leftInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
        | 1 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Defines the left partial interpolation proof `Lₓ`. -/
noncomputable def partialEquationLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match rule_def : (r 𝕏.α x) with
    | .topₗ _ _ => partialLeft_topₗ x rule_def
    | .topᵣ _ _ => partialLeft_topᵣ x rule_def
    | .axₗₗ _ _ _ => partialLeft_axₗₗ x rule_def
    | .axₗᵣ _ _ _ => partialLeft_axₗᵣ x rule_def
    | .axᵣₗ _ _ _ => partialLeft_axᵣₗ x rule_def
    | .axᵣᵣ _ _ _ => partialLeft_axᵣᵣ x rule_def
    | .orₗ _ _ _ _ => partialLeft_orₗ x rule_def
    | .orᵣ _ _ _ _ => partialLeft_orᵣ x rule_def
    | .andₗ _ _ _ _ => partialLeft_andₗ x rule_def
    | .andᵣ _ _ _ _ => partialLeft_andᵣ x rule_def
    | .boxₗ _ _ _ => partialLeft_boxₗ x rule_def
    | .boxᵣ _ _ _ => partialLeft_boxᵣ x rule_def

lemma partialEquationLeft_proves_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialEquationLeft x) (leftEquationSequent x) := by
    have 𝕏_h := 𝕏.step x
    unfold partialEquationLeft
    split <;> simp_all [Ext.Proves, Ext.r, List.map_eq_cons_iff]
    · simp [partialLeft_topₗ, Ext.f]
    · simp [partialLeft_topᵣ, Ext.f]
    · simp [partialLeft_axₗₗ, Ext.f]
    · simp [partialLeft_axₗᵣ, Ext.f]
    · simp [partialLeft_axᵣₗ, Ext.f]
    · simp [partialLeft_axᵣᵣ, Ext.f]
    · simp [partialLeft_orₗ]
      split <;> simp_all [Ext.f]
    · rename_i rule_def
      simp [partialLeft_orᵣ]
      have ⟨y, p_def, prop⟩ := 𝕏_h
      split <;> simp_all [Ext.f]
      simp [leftInterpolantSequent, leftEquationSequent, prop, rule_def]
      apply congrArg₂
      · simp [equation]; split <;> simp_all
      · simp [f, fₙ, fₚ]
        aesop
    · rename_i rule_def
      have ⟨y, z, p_def, prop⟩ := 𝕏_h
      simp [partialLeft_andₗ]
      split <;> simp_all
      have ⟨eq₁, eq₂⟩ := p_def
      by_cases eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z) <;> subst eq₁ eq₂
      · rw [dif_pos eq]
        simp [Ext.f]
      · rw [dif_neg eq]
        simp [Ext.f]
    · simp [partialLeft_andᵣ]
      split <;> simp_all [Ext.f]
    · simp [partialLeft_boxₗ]
      split <;> simp_all [Ext.f]
    · simp [partialLeft_boxᵣ]
      split <;> simp_all [Ext.f]

set_option maxHeartbeats 1000000 in
noncomputable def partialInterpolationLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
  then partialEquationLeft x
  else
    have equiv : Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x) := by
      have := (Interpolant_prop x ).1
      simp_all
    let 𝕐₁ := partialEquationLeft x
    let y₁ := 𝕐₁.root
    have y₁_prop := partialEquationLeft_proves_eq x
    let 𝕐₂ := equiv.1.choose
    let y₂ := equiv.1.choose_spec.choose
    have y₂_prop := equiv.1.choose_spec.choose_spec
    { X := Unit ⊕ 𝕐₁.X ⊕ 𝕐₂.X
      α | Sum.inl u => ⟨Ext.RuleApp.cutᵣ (leftInterpolantSequent x) (Interpolant 𝕏 (equation x)), [Sum.inr (Sum.inl y₁), Sum.inr (Sum.inr y₂)]⟩
        | Sum.inr (Sum.inl z₁) => ⟨Ext.r 𝕐₁.α z₁, List.map (Sum.inr ∘ Sum.inl) (Ext.p 𝕐₁.α z₁)⟩
        | Sum.inr (Sum.inr z₂) => ⟨Split_to_Ext (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩
      step
        | Sum.inl u => by
          simp only [Ext.r, Ext.T, Ext.p, List.map_cons, Split_to_Ext_f, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
          constructor
          · convert y₁_prop
            simp [leftEquationSequent, leftInterpolantSequent]
            aesop
          · convert y₂_prop using 1
            simp [leftInterpolantSequent]
            aesop
        | Sum.inr (Sum.inl z₁) => by
          have 𝕐₁_h := 𝕐₁.step z₁
          convert 𝕐₁_h <;> simp [Ext.p, Ext.r]
        | Sum.inr (Sum.inr z₂) => by
          have 𝕐₂_h := 𝕐₂.step z₂
          split
          all_goals
            rename_i eq
            cases r_def : r 𝕐₂.α z₂ <;> simp [Ext.r, r_def, Split_to_Ext] at eq
            all_goals
              simp [r_def] at 𝕐₂_h
              simp [Ext.p, 𝕐₂_h]
              all_goals
                convert 𝕐₂_h
                all_goals
                  try simp [r_def, Ext.r, Split_to_Ext_f, Split_to_Ext_fₙ]
                  try tauto
      root := Sum.inl ()
      path | Sum.inl u, f => by
              have := f.2.2 0
              simp [Ext.edge, Ext.p, f.2.1] at this
              rcases this with f1_def | f1_def
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [Ext.edge, Ext.p, fk_def] at step
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
                    · simp [Ext.edge, Ext.p, fk_def] at step
                      grind
                    · simp [fk_def] at ih
                let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 (n + 1)) (isRight n)) (isLeft n)
                have g_zero : g 0 = y₁ := by unfold g; simp [f1_def]
                have g_succ : ∀ n, Ext.edge 𝕐₁.α (g n) (g (n + 1)) := by
                  intro n
                  have step := f.2.2 (n + 1)
                  rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
                  · have := isRight n
                    simp [fn_def] at this
                  · simp [Ext.edge, Ext.p, fn_def] at step
                    simp [Ext.edge, Ext.p]
                    grind
                  · have := isLeft n
                    simp [fn_def] at this
                intro n
                have ⟨m, m_prop⟩ := 𝕐₁.path y₁ ⟨g, g_zero, g_succ⟩ n
                use m + 1
                convert m_prop
                unfold g
                simp [Ext.r]
                grind
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [Ext.edge, Ext.p, fk_def] at step
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
                    · simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fn_def] at step
                    simp [edge]
                    grind
                intro n
                have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
                use m + 1
                simp [Ext.r]
                rcases fn_def : f.1 (n + m + 1) with _ | _ | gn_def
                · have := isRight (n + m)
                  simp [fn_def] at this
                · have := isRight' (n + m)
                  simp [fn_def] at this
                · simp [←add_assoc, fn_def]
                  apply Split_to_Ext_isBox
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
                  simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
                    grind
                  · simp [fk_def] at ih
              let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 n) (isRight n)) (isLeft n)
              have g_zero : g 0 = z := by unfold g; simp [f.2.1]
              have g_succ : ∀ n, Ext.edge 𝕐₁.α (g n) (g (n + 1)) := by
                intro n
                have step := f.2.2 n
                rcases fn_def : f.1 n with _ | _ | gn_def
                · have := isRight n
                  simp [fn_def] at this
                · simp [Ext.edge, Ext.p, fn_def] at step
                  simp [Ext.edge, Ext.p]
                  grind
                · have := isLeft n
                  simp [fn_def] at this
              intro n
              have ⟨m, m_prop⟩ := 𝕐₁.path z ⟨g, g_zero, g_succ⟩ n
              use m
              convert m_prop
              unfold g
              simp [Ext.r]
              grind
           | Sum.inr (Sum.inr z), f => by
              have isRight : ∀ n, (f.1 n).isRight := by
                intro n
                induction n
                case zero => rw [f.2.1]; simp
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
                  simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
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
                · simp [Ext.edge, Ext.p, fn_def] at step
                  simp [edge]
                  grind
              intro n
              have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
              use m
              simp [Ext.r]
              rcases fn_def : f.1 (n + m) with _ | _ | gn_def
              · have := isRight (n + m)
                simp [fn_def] at this
              · have := isRight' (n + m)
                simp [fn_def] at this
              · apply Split_to_Ext_isBox
                convert m_prop
                unfold g
                simp [fn_def]}

/-- Every left partial interpolation proof `Lₓ` proves `f(x)ˡ ∣ ιₓ`. -/
lemma partialInterpolationLeft_proves_int {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialInterpolationLeft x) (leftInterpolantSequent x) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then (by
    convert partialEquationLeft_proves_eq x using 1
    · unfold partialInterpolationLeft
      simp [eq]
    · unfold leftInterpolantSequent leftEquationSequent
      simp [eq])
  else by
    unfold partialInterpolationLeft
    simp [eq]
    simp [Ext.Proves, Ext.r, Ext.f]

open Classical in
set_option maxHeartbeats 300000 in
/-- For every `x` in a finite split proof, the partial left interpolation proof associated with `x`
    has the property that on every path from the root to a non-axiomatic leaf, the box rule is
    applied on this path. -/
theorem partialInterpolationLeft_box_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  (r 𝕏.α x).isBox →
    ∀ (n : ℕ) (f : Fin (n + 1) → (partialInterpolationLeft x).X),
      f 0 = (partialInterpolationLeft x).root →
        (Ext.r (partialInterpolationLeft x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
          (∀ (m : Fin n), Ext.edge (partialInterpolationLeft x).α (f m.castSucc) (f m.succ)) →
            ∃ m, (Ext.r (partialInterpolationLeft x).α (f m)).isBox := by
  intro is_box n
  have 𝕏_h := 𝕏.step x
  cases r_def : r 𝕏.α x <;> simp_all [RuleApp.isBox]
  case boxₗ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold partialInterpolationLeft
      rw [dif_pos eq, partialEquationLeft]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [partialLeft_boxₗ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationLeft
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, Ext.edge, Ext.p] at step
        rcases step with l | r
        · rw [l]
          simp [Ext.r]
          simp [partialEquationLeft, partialLeft_boxₗ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp [Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_Ext_notNonAxLeaf 𝕏 x leftInterpolantSequent _ f_last
  case boxᵣ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold partialInterpolationLeft
      rw [dif_pos eq, partialEquationLeft]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [partialLeft_boxᵣ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationLeft
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, Ext.edge, Ext.p] at step
        rcases step with l | r
        · rw [l]
          simp [Ext.r]
          simp [partialEquationLeft, partialLeft_boxᵣ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp [Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_Ext_notNonAxLeaf 𝕏 x leftInterpolantSequent _ f_last

/-- Defining the left interpolation proof with all non-axiomatic nodes removed. -/
noncomputable def interpolantProofLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : ExtSkip.Proof :=
  @proofTransformation 𝕏 (@leftInterpolantSequent 𝕏 _) partialInterpolationLeft partialInterpolationLeft_proves_int partialInterpolationLeft_box_prop

/-- Left syntactic interpolation result! -/
theorem interpolantProofLeft_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
  : @interpolantProofLeft 𝕏 fin_X ⊢ leftInterpolantSequent x := by
  use ⟨x, (partialInterpolationLeft x).root⟩
  unfold interpolantProofLeft proofTransformation
  simp [proofTransformation_f]
  exact partialInterpolationLeft_proves_int x

/-! # Partial Left Interpolation Proofs

All of the left and right partial interpolation proofs, split apart based on rule application. These
are split apart since otherwise the file runs very slow. -/

noncomputable def partialRight_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
   : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topₗ (rightEquationSequent x) (by
      simp [rightEquationSequent, equation, rule_def]
      split <;> simp_all [Interpolant, partial_]
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialRight_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
      X := Unit
      α u := ⟨Ext.RuleApp.topᵣ (rightEquationSequent x) (by simp [rightEquationSequent, rule_def, f]; exact in_Δ), {}⟩
      step u := by simp [Ext.r, Ext.p]
      root := ()
      path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialRight_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topₗ (rightEquationSequent x) (by simp [rightEquationSequent, rule_def, f]; simp [equation]; split <;> simp_all [Interpolant, partial_]), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialRight_axₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axₗᵣ (rightEquationSequent x) n (by
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
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialRight_axᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axᵣₗ (rightEquationSequent x) n (by
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
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialRight_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axᵣᵣ (rightEquationSequent x) n (by simp [rightEquationSequent, rule_def, f, in_Δ]), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exfalso; simp [Ext.edge, Ext.p] at f; exact f.2

noncomputable def partialRight_orₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
: Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
          rw [equation]
          split <;> simp_all
        { X := Unit
          α u := ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
          step := by simp [Ext.r, Ext.p]
          root := ()
          path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
        | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
        | y :: z :: l => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialRight_orᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
    | [y] =>
      have interpolant_eq : Interpolant 𝕏 (equation x) = Interpolant 𝕏 (at encodeVar y) := by
        rw [equation]
        split <;> simp_all
    { X := Fin 2
      α | 0 => ⟨Ext.RuleApp.orᵣ (rightEquationSequent x) φ ψ (by simp [rightEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step := by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        intro n
        match n with
          | 0 =>
            simp [Ext.r, Ext.p, Ext.T, Ext.f, Ext.fₙ, Ext.fₚ, rightInterpolantSequent, rightEquationSequent, rule_def, 𝕏_h, interpolant_eq]
            aesop -- big aesop
          | 1 =>
            simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
    | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialRight_andₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) v Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨Ext.RuleApp.andₗ (rightEquationSequent x) (~ (Interpolant 𝕏 (at encodeVar y))) (~ (Interpolant 𝕏 (at encodeVar z))) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1,2]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
        | 2 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [Ext.r, Ext.p, rightEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
          constructor <;> ext <;> simp [f] <;> aesop
        | 1 => by simp [Ext.r, Ext.p]
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

set_option maxHeartbeats 400000 in
noncomputable def partialRight_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = (Interpolant 𝕏 (at encodeVar y) & Interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    if eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z)
    then {
    X := Fin 4
    α | 0 => ⟨Ext.RuleApp.orₗ (rightEquationSequent x) (~Interpolant 𝕏 (at encodeVar y)) (~Interpolant 𝕏 (at encodeVar z)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨Ext.RuleApp.andᵣ (((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {(Sum.inl $ ~Interpolant 𝕏 (at encodeVar y)), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)}) φ ψ (by simp [rightEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 3 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
      | 1 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [Ext.r, Ext.p, rightEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, rightInterpolantSequent, 𝕏_h, eq]
        constructor <;> ext <;> simp [f] <;> aesop
      | 2 => by simp [Ext.r, Ext.p]
      | 3 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    else {
    X := Fin 6
    α | 0 => ⟨Ext.RuleApp.orₗ (rightEquationSequent x) (~Interpolant 𝕏 (at encodeVar y)) (~Interpolant 𝕏 (at encodeVar z)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 => ⟨Ext.RuleApp.andᵣ (((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {(Sum.inl $ ~Interpolant 𝕏 (at encodeVar y)), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)}) φ ψ (by simp [rightEquationSequent, rule_def, f, interpolant_eq, in_Δ]), [2,3]⟩
      | 2 => ⟨Ext.RuleApp.wkₗ ((((((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {Sum.inl $ ~Interpolant 𝕏 (at encodeVar y), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)})) \ {Sum.inr (φ & ψ)}) ∪ {Sum.inr φ}) (~Interpolant 𝕏 (at encodeVar z)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [4]⟩
      | 3 => ⟨Ext.RuleApp.wkₗ ((((((rightEquationSequent x) \ {Sum.inl $ ~Interpolant 𝕏 (equation x)}) ∪ {Sum.inl $ ~Interpolant 𝕏 (at encodeVar y), Sum.inl $ ~Interpolant 𝕏 (at encodeVar z)})) \ {Sum.inr (φ & ψ)}) ∪ {Sum.inr ψ}) (~Interpolant 𝕏 (at encodeVar y)) (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [5]⟩
      | 4 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 5 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
      | 1 => by simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
      | 2 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [Ext.r, Ext.p, rightEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
        ext ψ
        rcases ψ with ψ | ψ <;> simp [f]
        constructor <;> try tauto
        intro mp; subst mp; simp_all
        intro con; apply eq; apply Formula.neg_eq; exact con
      | 3 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
        simp [Ext.r, Ext.p, rightEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
        ext ψ
        rcases ψ with ψ | ψ <;> simp [f]
        constructor <;> try tauto
        intro mp; subst mp; simp_all
        intro con; apply eq; apply Formula.neg_eq; exact Eq.symm con
      | 4 => by simp [Ext.r, Ext.p]
      | 5 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialRight_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = ◇ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 2
      α | 0 => ⟨Ext.RuleApp.boxₗ (rightEquationSequent x) (~(Interpolant 𝕏 (at encodeVar y))) (by simp [rightEquationSequent, interpolant_eq]), [1]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [Ext.r, Ext.p, rightEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
        | 1 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

noncomputable def partialRight_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq : Interpolant 𝕏 (equation x) = □ (Interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [Interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 => ⟨Ext.RuleApp.boxᵣ (rightEquationSequent x) φ (by simp [rightEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨Ext.RuleApp.wkₗ (((rightEquationSequent x) \ {Sum.inr $ □ φ}).D ∪ {Sum.inr φ}) (◇ (~(Interpolant 𝕏 (at encodeVar y)))) (by simp [rightEquationSequent, rule_def, f, interpolant_eq, SplitSequent.D, SplitFormula.isDiamond]), [2]⟩
        | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f, Ext.fₙ_alternate]
        | 1 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
          simp [Ext.r, Ext.p, rightEquationSequent, rule_def, interpolant_eq, Ext.f, Ext.fₙ_alternate, rightInterpolantSequent, 𝕏_h]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
          simp [SplitFormula.isDiamond]
          constructor <;> try tauto
          intro mp
          subst mp
          simp
          induction Interpolant 𝕏 (at encodeVar y) <;> simp_all -- MALVIN so weird
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Defines the right partial interpolation proof `Rₓ`. -/
noncomputable def partialEquationRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match rule_def : (r 𝕏.α x) with
    | .topₗ _ _ => partialRight_topₗ x rule_def
    | .topᵣ _ _ => partialRight_topᵣ x rule_def
    | .axₗₗ _ _ _ => partialRight_axₗₗ x rule_def
    | .axₗᵣ _ _ _ => partialRight_axₗᵣ x rule_def
    | .axᵣₗ _ _ _ => partialRight_axᵣₗ x rule_def
    | .axᵣᵣ _ _ _ => partialRight_axᵣᵣ x rule_def
    | .orₗ _ _ _ _ => partialRight_orₗ x rule_def
    | .orᵣ _ _ _ _ => partialRight_orᵣ x rule_def
    | .andₗ _ _ _ _ => partialRight_andₗ x rule_def
    | .andᵣ _ _ _ _ => partialRight_andᵣ x rule_def
    | .boxₗ _ _ _ => partialRight_boxₗ x rule_def
    | .boxᵣ _ _ _ => partialRight_boxᵣ x rule_def

/-- Every right partial interpolation proof `Rₓ` proves `~ιₓ ∣ f(x)ʳ`. -/
lemma partialEquationRight_proves_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialEquationRight x) (rightEquationSequent x) := by
    have 𝕏_h := 𝕏.step x
    unfold partialEquationRight
    split <;> simp_all [Ext.Proves, Ext.r, List.map_eq_cons_iff]
    · simp [partialRight_topₗ, Ext.f]
    · simp [partialRight_topᵣ, Ext.f]
    · simp [partialRight_axₗₗ, Ext.f]
    · simp [partialRight_axₗᵣ, Ext.f]
    · simp [partialRight_axᵣₗ, Ext.f]
    · simp [partialRight_axᵣᵣ, Ext.f]
    · rename_i rule_def
      simp [partialRight_orₗ]
      have ⟨y, p_def, prop⟩ := 𝕏_h
      split <;> simp_all [Ext.f]
      simp [rightInterpolantSequent, rightEquationSequent, prop, rule_def]
      apply congrArg₂
      · simp [equation]; split <;> simp_all
      · simp [f, fₙ, fₚ]
        aesop
    · simp [partialRight_orᵣ]
      split <;> simp_all [Ext.f]
    · simp [partialRight_andₗ]
      split <;> simp_all [Ext.f]
    · rename_i rule_def
      have ⟨y, z, p_def, prop⟩ := 𝕏_h
      simp [partialRight_andᵣ]
      split <;> simp_all
      have ⟨eq₁, eq₂⟩ := p_def
      by_cases eq : Interpolant 𝕏 (at encodeVar y) = Interpolant 𝕏 (at encodeVar z) <;> subst eq₁ eq₂
      · rw [dif_pos eq]
        simp [Ext.f]
      · rw [dif_neg eq]
        simp [Ext.f]
    · simp [partialRight_boxₗ]
      split <;> simp_all [Ext.f]
    · simp [partialRight_boxᵣ]
      split <;> simp_all [Ext.f]

set_option maxHeartbeats 1000000 in
noncomputable def partialInterpolationRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
  then partialEquationRight x
  else
    have equiv : Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x) := by
      have := (Interpolant_prop x).1
      simp_all
    let 𝕐₁ := partialEquationRight x
    let y₁ := 𝕐₁.root
    have y₁_prop := partialEquationRight_proves_eq x
    let 𝕐₂ := equiv.2.choose
    let y₂ := equiv.2.choose_spec.choose
    have y₂_prop := equiv.2.choose_spec.choose_spec
    { X := Unit ⊕ 𝕐₁.X ⊕ 𝕐₂.X
      α | Sum.inl u => ⟨Ext.RuleApp.cutₗ (rightInterpolantSequent x) (~Interpolant 𝕏 (equation x)), [Sum.inr (Sum.inl y₁), Sum.inr (Sum.inr y₂)]⟩
        | Sum.inr (Sum.inl z₁) => ⟨Ext.r 𝕐₁.α z₁, List.map (Sum.inr ∘ Sum.inl) (Ext.p 𝕐₁.α z₁)⟩
        | Sum.inr (Sum.inr z₂) => ⟨Split_to_Ext (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩
      step
        | Sum.inl u => by
          simp only [Ext.r, Ext.T, Ext.p, List.map_cons, Split_to_Ext_f, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
          constructor
          · convert y₁_prop
            simp [rightEquationSequent, rightInterpolantSequent]
            aesop
          · convert y₂_prop using 1
            simp [rightInterpolantSequent]
            aesop
        | Sum.inr (Sum.inl z₁) => by
          have 𝕐₁_h := 𝕐₁.step z₁
          convert 𝕐₁_h <;> simp [Ext.p, Ext.r]
        | Sum.inr (Sum.inr z₂) => by
          have 𝕐₂_h := 𝕐₂.step z₂
          split
          all_goals
            rename_i eq
            cases r_def : r 𝕐₂.α z₂ <;> simp [Ext.r, r_def, Split_to_Ext] at eq
            all_goals
              simp [r_def] at 𝕐₂_h
              simp [Ext.p, 𝕐₂_h]
              all_goals
                convert 𝕐₂_h
                all_goals
                  try simp [r_def, Ext.r, Split_to_Ext_f, Split_to_Ext_fₙ]
                  try tauto
      root := Sum.inl ()
      path | Sum.inl u, f => by
              have := f.2.2 0
              simp [Ext.edge, Ext.p, f.2.1] at this
              rcases this with f1_def | f1_def
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [Ext.edge, Ext.p, fk_def] at step
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
                    · simp [Ext.edge, Ext.p, fk_def] at step
                      grind
                    · simp [fk_def] at ih
                let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 (n + 1)) (isRight n)) (isLeft n)
                have g_zero : g 0 = y₁ := by unfold g; simp [f1_def]
                have g_succ : ∀ n, Ext.edge 𝕐₁.α (g n) (g (n + 1)) := by
                  intro n
                  have step := f.2.2 (n + 1)
                  rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
                  · have := isRight n
                    simp [fn_def] at this
                  · simp [Ext.edge, Ext.p, fn_def] at step
                    simp [Ext.edge, Ext.p]
                    grind
                  · have := isLeft n
                    simp [fn_def] at this
                intro n
                have ⟨m, m_prop⟩ := 𝕐₁.path y₁ ⟨g, g_zero, g_succ⟩ n
                use m + 1
                convert m_prop
                unfold g
                simp [Ext.r]
                grind
              · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
                  intro n
                  induction n
                  case zero => rw [f1_def]; simp
                  case succ k ih =>
                    have step := f.2.2 (k + 1)
                    rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
                    simp [Ext.edge, Ext.p, fk_def] at step
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
                    · simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fn_def] at step
                    simp [edge]
                    grind
                intro n
                have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
                use m + 1
                simp [Ext.r]
                rcases fn_def : f.1 (n + m + 1) with _ | _ | gn_def
                · have := isRight (n + m)
                  simp [fn_def] at this
                · have := isRight' (n + m)
                  simp [fn_def] at this
                · simp [←add_assoc, fn_def]
                  apply Split_to_Ext_isBox
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
                  simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
                    grind
                  · simp [fk_def] at ih
              let g : ℕ → 𝕐₁.X := fun n ↦ Sum.getLeft (Sum.getRight (f.1 n) (isRight n)) (isLeft n)
              have g_zero : g 0 = z := by unfold g; simp [f.2.1]
              have g_succ : ∀ n, Ext.edge 𝕐₁.α (g n) (g (n + 1)) := by
                intro n
                have step := f.2.2 n
                rcases fn_def : f.1 n with _ | _ | gn_def
                · have := isRight n
                  simp [fn_def] at this
                · simp [Ext.edge, Ext.p, fn_def] at step
                  simp [Ext.edge, Ext.p]
                  grind
                · have := isLeft n
                  simp [fn_def] at this
              intro n
              have ⟨m, m_prop⟩ := 𝕐₁.path z ⟨g, g_zero, g_succ⟩ n
              use m
              convert m_prop
              unfold g
              simp [Ext.r]
              grind
           | Sum.inr (Sum.inr z), f => by
              have isRight : ∀ n, (f.1 n).isRight := by
                intro n
                induction n
                case zero => rw [f.2.1]; simp
                case succ k ih =>
                  have step := f.2.2 k
                  rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
                  simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
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
                · simp [Ext.edge, Ext.p, fn_def] at step
                  simp [edge]
                  grind
              intro n
              have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
              use m
              simp [Ext.r]
              rcases fn_def : f.1 (n + m) with _ | _ | gn_def
              · have := isRight (n + m)
                simp [fn_def] at this
              · have := isRight' (n + m)
                simp [fn_def] at this
              · apply Split_to_Ext_isBox
                convert m_prop
                unfold g
                simp [fn_def]}

lemma partialInterpolationRight_proves_int {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialInterpolationRight x) (rightInterpolantSequent x) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then (by
    convert partialEquationRight_proves_eq x using 1
    · unfold partialInterpolationRight
      simp [eq]
    · unfold rightInterpolantSequent rightEquationSequent
      simp [eq])
  else by
    unfold partialInterpolationRight
    simp [eq]
    simp [Ext.Proves, Ext.r, Ext.f]

open Classical in
set_option maxHeartbeats 300000 in
/-- For every `x` in a finite split proof, the partial left interpolation proof associated with `x`
    has the property that on every path from the root to a non-axiomatic leaf, the box rule is
    applied on this path. -/
theorem partialInterpolationRight_box_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  (r 𝕏.α x).isBox →
    ∀ (n : ℕ) (f : Fin (n + 1) → (partialInterpolationRight x).X),
      f 0 = (partialInterpolationRight x).root →
        (Ext.r (partialInterpolationRight x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
          (∀ (m : Fin n), Ext.edge (partialInterpolationRight x).α (f m.castSucc) (f m.succ)) →
            ∃ m, (Ext.r (partialInterpolationRight x).α (f m)).isBox := by
  intro is_box n
  have 𝕏_h := 𝕏.step x
  cases r_def : r 𝕏.α x <;> simp_all [RuleApp.isBox]
  case boxₗ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold partialInterpolationRight
      rw [dif_pos eq, partialEquationRight]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [partialRight_boxₗ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationRight
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, Ext.edge, Ext.p] at step
        rcases step with l | r
        · rw [l]
          simp [Ext.r]
          simp [partialEquationRight, partialRight_boxₗ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp [Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_Ext_notNonAxLeaf 𝕏 x rightInterpolantSequent _ f_last
  case boxᵣ =>
    by_cases eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
    · unfold partialInterpolationRight
      rw [dif_pos eq, partialEquationRight]
      split <;> simp_all
      intro f f_zero f_last f_succ
      use 0
      simp [partialRight_boxᵣ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationRight
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp [f_zero, Ext.edge, Ext.p] at step
        rcases step with l | r
        · rw [l]
          simp [Ext.r]
          simp [partialEquationRight, partialRight_boxᵣ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp [Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · simp [Ext.edge, Ext.p, fk_def] at step
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
                  · simp [Ext.edge, Ext.p, fk_def] at step
                    grind
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · simp [f_last_def] at f_last
            exact @Split_to_Ext_notNonAxLeaf 𝕏 x rightInterpolantSequent _ f_last

/-- Defining the right interpolation proof with all non-axiomatic nodes removed. -/
noncomputable def interpolantProofRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : ExtSkip.Proof :=
  @proofTransformation 𝕏 (@rightInterpolantSequent 𝕏 _) partialInterpolationRight partialInterpolationRight_proves_int partialInterpolationRight_box_prop

/-- Right syntactic interpolation result! -/
theorem interpolantProofRight_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
  : @interpolantProofRight 𝕏 fin_X ⊢ rightInterpolantSequent x := by
  use ⟨x, (partialInterpolationRight x).root⟩
  unfold interpolantProofRight proofTransformation
  simp [proofTransformation_f]
  exact partialInterpolationRight_proves_int x


/-- ## Syntactic interpolation

Given a finite split proof, `interpolantProofLeft` proves the left interpolation correctness
statement and `interpolantProofRight` proves the right interpolation correctness statement. -/

theorem syntacticInterpolation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    (@interpolantProofLeft 𝕏 fin_X  ⊢ leftInterpolantSequent  x)
  ∧ (@interpolantProofRight 𝕏 fin_X ⊢ rightInterpolantSequent x) :=
  ⟨interpolantProofLeft_proves_interpolant x, interpolantProofRight_proves_interpolant x⟩
