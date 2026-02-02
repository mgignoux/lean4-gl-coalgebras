import GL.Logic
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Interpolants
import GL.SplitCutCoalgebraProof

namespace CutPre

inductive RuleApp {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent)
  | pre : (y : 𝕏.X) → (y ∈ Split.p 𝕏.α x) → RuleApp x τ
  | cutₗ : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ
  | cutᵣ : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ
  | wkₗ : (Δ : SplitSequent) → (A : Formula) → (Sum.inl A) ∈ Δ → RuleApp x τ
  | wkᵣ : (Δ : SplitSequent) → (A : Formula) → (Sum.inr A) ∈ Δ → RuleApp x τ
  | topₗ : (Δ : SplitSequent) → (Sum.inl ⊤) ∈ Δ → RuleApp x τ
  | topᵣ : (Δ : SplitSequent) → (Sum.inr ⊤) ∈ Δ → RuleApp x τ
  | axₗₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp x τ
  | axₗᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp x τ
  | axᵣₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp x τ
  | axᵣᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp x τ
  | andₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A & B) ∈ Δ → RuleApp x τ
  | andᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A & B) ∈ Δ → RuleApp x τ
  | orₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A v B) ∈ Δ → RuleApp x τ
  | orᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A v B) ∈ Δ → RuleApp x τ
  | boxₗ : (Δ : SplitSequent) → (A : Formula) → Sum.inl (□ A) ∈ Δ → RuleApp x τ
  | boxᵣ : (Δ : SplitSequent) → (A : Formula) → Sum.inr (□ A) ∈ Δ → RuleApp x τ

def fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent
  | RuleApp.pre _ _ => ∅
  | RuleApp.cutₗ _ _ => ∅
  | RuleApp.cutᵣ _ _ => ∅
  | RuleApp.wkₗ _ A _ => {Sum.inl A}
  | RuleApp.wkᵣ _ A _ => {Sum.inr A}
  | RuleApp.topₗ _ _ => {Sum.inl ⊤}
  | RuleApp.topᵣ _ _ => {Sum.inr ⊤}
  | RuleApp.axₗₗ _ n _ => {Sum.inl $ at n, Sum.inl $ na n}
  | RuleApp.axₗᵣ _ n _ => {Sum.inl $ at n, Sum.inr $ na n}
  | RuleApp.axᵣₗ _ n _ => {Sum.inr $ at n, Sum.inl $ na n}
  | RuleApp.axᵣᵣ _ n _ => {Sum.inr $ at n, Sum.inr $ na n}
  | RuleApp.andₗ _ A B _ => {Sum.inl (A & B)}
  | RuleApp.andᵣ _ A B _ => {Sum.inr (A & B)}
  | RuleApp.orₗ _ A B _ => {Sum.inl (A v B)}
  | RuleApp.orᵣ _ A B _ => {Sum.inr (A v B)}
  | RuleApp.boxₗ _ A _ => {Sum.inl (□ A)}
  | RuleApp.boxᵣ _ A _ => {Sum.inr (□ A)}

def f {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent
  | RuleApp.pre y _ => τ y
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ _ _ => Δ
  | RuleApp.wkᵣ Δ _ _ => Δ
  | RuleApp.topₗ Δ _ => Δ
  | RuleApp.topᵣ Δ _ => Δ
  | RuleApp.axₗₗ Δ _ _ => Δ
  | RuleApp.axₗᵣ Δ _ _ => Δ
  | RuleApp.axᵣₗ Δ _ _ => Δ
  | RuleApp.axᵣᵣ Δ _ _ => Δ
  | RuleApp.andₗ Δ _ _ _ => Δ
  | RuleApp.andᵣ Δ _ _ _ => Δ
  | RuleApp.orₗ Δ _ _ _ => Δ
  | RuleApp.orᵣ Δ _ _ _ => Δ
  | RuleApp.boxₗ Δ _ _ => Δ
  | RuleApp.boxᵣ Δ _ _ => Δ

def fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent := fun r ↦ f r \ fₚ r

theorem fₙ_alternate {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (r : RuleApp x τ) : fₙ r = match r with
  | RuleApp.pre y _ => τ y
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ A _ =>  Δ \ {Sum.inl A}
  | RuleApp.wkᵣ Δ A _ =>  Δ \ {Sum.inr A}
  | RuleApp.topₗ Δ _ => Δ \ {Sum.inl ⊤}
  | RuleApp.topᵣ Δ _ => Δ \ {Sum.inr ⊤}
  | RuleApp.axₗₗ Δ n _ => Δ \ {Sum.inl $ at n, Sum.inl $ na n}
  | RuleApp.axₗᵣ Δ n _ => Δ \ {Sum.inl $ at n, Sum.inr $ na n}
  | RuleApp.axᵣₗ Δ n _ => Δ \ {Sum.inr $ at n, Sum.inl $ na n}
  | RuleApp.axᵣᵣ Δ n _ => Δ \ {Sum.inr $ at n, Sum.inr $ na n}
  | RuleApp.andₗ Δ A B _ => Δ \ {Sum.inl (A & B)}
  | RuleApp.andᵣ Δ A B _ => Δ \ {Sum.inr (A & B)}
  | RuleApp.orₗ Δ A B _ => Δ \ {Sum.inl (A v B)}
  | RuleApp.orᵣ Δ A B _ => Δ \ {Sum.inr (A v B)}
  | RuleApp.boxₗ Δ A _ => Δ \ {Sum.inl (□ A)}
  | RuleApp.boxᵣ Δ A _ => Δ \ {Sum.inr (□ A)} := by cases r <;> simp [fₙ, f, fₚ]

universe u
@[simp] def T {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨λ X ↦ ((RuleApp x τ × List X) : Type u), by rintro X Y f ⟨r, A⟩; exact ⟨r, A.map f⟩, by aesop_cat, by aesop_cat⟩

def r {X : Type u} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (α : X → (T x τ).obj X) (x : X) := (α x).1
def p {X : Type u} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (α : X → (T x τ).obj X) (x : X) := (α x).2
def edge  {X : Type u} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (α : X → (T x τ).obj X) (x y : X) : Prop := y ∈ p α x

def RuleApp.isBox {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : RuleApp x τ → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

structure CutProofFromPremises {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) where
  X : Type
  α : X → (T x τ).obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.pre _ _ => p α x = []
    | RuleApp.cutₗ _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).filter_right ∪ {Sum.inl $ A}, (fₙ (r α x)).filter_left ∪ {Sum.inr $ ~A}]
    | RuleApp.cutᵣ _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).filter_left ∪ {Sum.inr $ A}, (fₙ (r α x)).filter_right ∪ {Sum.inl $ ~A}]
    | RuleApp.wkₗ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.wkᵣ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.topₗ _ _ => p α x = ∅
    | RuleApp.topᵣ _ _ => p α x = ∅
    | RuleApp.axₗₗ _ _ _ => p α x = ∅
    | RuleApp.axₗᵣ _ _ _ => p α x = ∅
    | RuleApp.axᵣₗ _ _ _ => p α x = ∅
    | RuleApp.axᵣᵣ _ _ _ => p α x = ∅
    | RuleApp.andₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inr A}]
  root : X
  root_prop : f (r α root) = τ x
  path : ∀ x, ∀ f : {f : ℕ → X // f 0 = x ∧ ∀ (n : ℕ), edge α (f n) (f (n + 1))},
    ∀ n, ∃ m, (r α (f.1 (n + m))).isBox

def CutProofFromPremises.Proves {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (𝕐 : CutProofFromPremises x τ) (Δ : SplitSequent) : Prop := ∃ x : 𝕐.X, f (r 𝕐.α x) = Δ
infixr:6 "⊢" => CutProofFromPremises.Proves

end CutPre

namespace Split

noncomputable def leftInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (at (encodeVar x)))} ∪ (SplitSequent.filter_left (f (r 𝕏.α x)))

noncomputable def leftEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (equation x))} ∪ (SplitSequent.filter_left (f (r 𝕏.α x)))


noncomputable def rightInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (Interpolant 𝕏 (at (encodeVar x))))} ∪ (SplitSequent.filter_right (f (r 𝕏.α x)))

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

theorem Split_to_CutPre_f {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : CutPre.f (@Split_to_CutPre _ x τ r) = f r := by
  unfold Split_to_CutPre
  cases r <;> simp [f, CutPre.f]

theorem Split_to_CutPre_fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : CutPre.fₚ (@Split_to_CutPre _ x τ r) = fₚ r := by
  unfold Split_to_CutPre
  cases r <;> simp [fₚ, CutPre.fₚ]

theorem Split_to_CutPre_fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) : CutPre.fₙ (@Split_to_CutPre _ x τ r) = fₙ r := by
  unfold Split_to_CutPre
  cases r <;> simp [fₙ_alternate, CutPre.fₙ_alternate]

/-
-------------- ax
f^l(x) | I(χx)       ~I(χx) | ,I(px)
----------------------------------- cutᵣ
         f^l(x) | I(px)

-/

/- PARTIAL INTERPOLANT PROOFS. I SPLIT THESE APART BECAUSE THEY RUN SO SLOW OTHERWISE -/
noncomputable def PartialLeft_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.topₗ (leftInterpolantSequent x) (by simp [leftInterpolantSequent, rule_def, f, in_Δ]), {}⟩
    h u := by simp [CutPre.r, CutPre.p]
    root := ()
    root_prop := by simp [CutPre.f, CutPre.r]
    path u f := by sorry}
  else
    have eq_or_equiv := (Interpolant_prop x).1
    have equiv : Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x) := by simp_all
    let 𝕐 := equiv.1.choose
    have 𝕐_prop  := equiv.1.choose_spec
    let y := 𝕐_prop.choose
    have y_prop := 𝕐_prop.choose_spec
    { X := Fin 2 ⊕ 𝕐.X
      α | Sum.inl 0 => ⟨CutPre.RuleApp.cutᵣ (leftInterpolantSequent x) (Interpolant 𝕏 (equation x)), [Sum.inl 1, Sum.inr y]⟩
        | Sum.inl 1 => ⟨CutPre.RuleApp.topₗ (leftEquationSequent x) (by simp [leftEquationSequent, equation, rule_def, f, in_Δ]), {}⟩
        | Sum.inr z => ⟨Split_to_CutPre (r 𝕐.α z), List.map Sum.inr (p 𝕐.α z)⟩
      h | Sum.inl 0 => by
          simp [Split_to_CutPre_f, CutPre.r, CutPre.p]
          constructor
          · simp [CutPre.f, leftEquationSequent, CutPre.fₙ_alternate, leftInterpolantSequent]
            aesop
          · unfold 𝕐 y
            simp [y_prop, CutPre.fₙ_alternate, leftInterpolantSequent]
            aesop
        | Sum.inl 1 => by simp [CutPre.r, CutPre.p]
        | Sum.inr z => by
          have 𝕐_h := 𝕐.h z
          simp [Split_to_CutPre_f, Split_to_CutPre_fₙ, CutPre.r, CutPre.p]
          cases rz_def : r 𝕐.α z <;> simp_all only <;> rw [Split_to_CutPre] <;> simp_all <;> try simp [←𝕐_h, Split_to_CutPre_f]
      root := Sum.inl 0
      root_prop := by sorry
      path := by sorry
      }

noncomputable def PartialLeft_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.topᵣ (leftInterpolantSequent x) (by
      simp [leftInterpolantSequent, eq, equation, rule_def] -- why not able to simpe with rule here
      split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    root_prop := by sorry
    path := by sorry}
  else
    have eq_or_equiv := (Interpolant_prop x).1
    have equiv : Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x) := by simp_all
    let 𝕐 := equiv.1.choose
    have 𝕐_prop  := equiv.1.choose_spec
    let y := 𝕐_prop.choose
    have y_prop := 𝕐_prop.choose_spec
    { X := Fin 2 ⊕ 𝕐.X
      α | Sum.inl 0 => ⟨CutPre.RuleApp.cutᵣ (leftInterpolantSequent x) (Interpolant 𝕏 (equation x)), [Sum.inl 1, Sum.inr y]⟩
        | Sum.inl 1 => ⟨CutPre.RuleApp.topᵣ (leftEquationSequent x) (by
          simp [leftEquationSequent, equation, rule_def]
          split <;> simp_all [Interpolant, partial_]
      ), {}⟩
        | Sum.inr z => ⟨Split_to_CutPre (r 𝕐.α z), List.map Sum.inr (p 𝕐.α z)⟩
      h | Sum.inl 0 => by
          simp [Split_to_CutPre_f, CutPre.r, CutPre.p]
          constructor
          · simp [CutPre.f, leftEquationSequent, CutPre.fₙ_alternate, leftInterpolantSequent]
            aesop
          · unfold 𝕐 y
            simp [y_prop, CutPre.fₙ_alternate, leftInterpolantSequent]
            aesop
        | Sum.inl 1 => by simp [CutPre.r, CutPre.p]
        | Sum.inr z => by
          have 𝕐_h := 𝕐.h z
          simp [Split_to_CutPre_f, Split_to_CutPre_fₙ, CutPre.r, CutPre.p]
          cases rz_def : r 𝕐.α z <;> simp_all only <;> rw [Split_to_CutPre] <;> simp_all <;> try simp [←𝕐_h, Split_to_CutPre_f]
      root := by sorry
      root_prop := by sorry
      path := by sorry}


noncomputable def PartialLeft_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.axₗₗ (leftInterpolantSequent x) n (by simp [leftInterpolantSequent, rule_def, f, in_Δ]), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    root_prop := by sorry
    path := by sorry}
  else sorry

noncomputable def PartialLeft_axₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.axₗᵣ (leftInterpolantSequent x) n (by
      simp [leftInterpolantSequent, rule_def, f, in_Δ, eq]
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
    h := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    root_prop := by sorry
    path := by sorry}
  else sorry

noncomputable def PartialLeft_axᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.axᵣₗ (leftInterpolantSequent x) n (by
      simp [leftInterpolantSequent, rule_def, f, in_Δ, eq]
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
    h := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    root_prop := by sorry
    path := by sorry}
  else sorry

noncomputable def PartialLeft_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.topᵣ (leftInterpolantSequent x) (by
      simp [leftInterpolantSequent, rule_def, f, eq, equation]
      split <;> simp_all [Interpolant, partial_]
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]
    root := ()
    root_prop := by sorry
    path := by sorry}
  else sorry

/-
If Iₓ := φ v ψ then theres an issue because we do not want to split Iₓ, we want to use Iₓ = Iy.
so basically we want to allow the focused principal to be in the Sequent

Can we weaken? No that works the other way around.

Another option is to prove interpolant can not be formula? But this is unlikely

φ, ψ, fₙˡ x,
------------
φ v ψ, fₙˡ x



 --------------- as(y)
  φ, ψ, fₙˡ x, Iₓ -- condition is: |f(y)| = |fₙ(x) ∪ {φ,ψ}| and
----------------- ∨ₗ
`φ v ψ`, fₙˡ x, Iₓ


  --------------------
  φ,ψ,fn x' / Iy & Iy,  Iy
  -------------------- andl
   φ,ψ,fₙ x', Iy & Iy
--------------------- ∨ₗ -- Are we gonna do multiset???????
`φ ∨ ψ`, fₙ x', Iy & Iy

-/
noncomputable def PartialLeft_orₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq : Interpolant 𝕏 (at encodeVar x) = Interpolant 𝕏 (at encodeVar y) := by
          rw [eq, equation]
          split <;> simp_all
        { X := Fin 2
          α u :=
            match u with
            | 0 => ⟨CutPre.RuleApp.orₗ (leftInterpolantSequent x) φ ψ (by simp [leftInterpolantSequent, rule_def, f, in_Δ]), [1]⟩
            | 1 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
          h := by
            have 𝕏_h := 𝕏.h x
            simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq, and_true, fₙ_alternate] at 𝕏_h
            intro n
            match n with
              | 0 =>
                simp [CutPre.r, CutPre.p, CutPre.T, CutPre.f, CutPre.fₙ, CutPre.fₚ, leftInterpolantSequent, rule_def, 𝕏_h]
                aesop -- big aesop
              | 1 =>
                simp [CutPre.r, CutPre.p]
          root := sorry
          root_prop := by sorry
          path := by sorry}
        | _ => sorry -- not possible
  else sorry

noncomputable def PartialLeft_orᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
      | [y] =>
      if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
        X := Unit
        α u := ⟨CutPre.RuleApp.pre y (by simp [p_def])
          , {}⟩
        h := by simp [CutPre.r, CutPre.p]
        root := sorry
        root_prop := by sorry
        path := by sorry}
      else sorry
        | _ => sorry

noncomputable def PartialLeft_andₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
    root := sorry
    root_prop := sorry
    path := by sorry}
  else sorry

noncomputable def PartialLeft_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
    root := sorry
    root_prop := sorry
    path := by sorry}
  else sorry

noncomputable def PartialLeft_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
    root := sorry
    root_prop := sorry
    path := by sorry}
  else sorry

noncomputable def PartialLeft_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
    root := sorry
    root_prop := sorry
    path := by sorry}
  else sorry


noncomputable def PartialInterpolationLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
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

def ProofTranslationMap {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) : (y : 𝕏.X) × (PartialProof y).X → SplitCut.T.obj ((y : 𝕏.X) × (PartialProof y).X) :=
  fun ⟨y, z_y⟩ ↦
  match (@CutPre.r _ _ _ _ (PartialProof y).α z_y) with
  | .pre z _ => ⟨SplitCut.RuleApp.skp (σ z), [⟨z, (PartialProof z).root⟩]⟩ -- map to the root
  | .cutₗ Δ A => ⟨SplitCut.RuleApp.cutₗ Δ A, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .cutᵣ Δ A => ⟨SplitCut.RuleApp.cutᵣ Δ A, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .wkₗ Δ A in_Δ => ⟨SplitCut.RuleApp.wkₗ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .wkᵣ Δ A in_Δ => ⟨SplitCut.RuleApp.wkᵣ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .topₗ Δ in_Δ => ⟨SplitCut.RuleApp.topₗ Δ in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .topᵣ Δ in_Δ => ⟨SplitCut.RuleApp.topᵣ Δ in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axₗₗ Δ n in_Δ => ⟨SplitCut.RuleApp.axₗₗ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axₗᵣ Δ n in_Δ => ⟨SplitCut.RuleApp.axₗᵣ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axᵣₗ Δ n in_Δ => ⟨SplitCut.RuleApp.axᵣₗ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axᵣᵣ Δ n in_Δ => ⟨SplitCut.RuleApp.axᵣᵣ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .andₗ Δ A B in_Δ => ⟨SplitCut.RuleApp.andₗ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .andᵣ Δ A B in_Δ => ⟨SplitCut.RuleApp.andᵣ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .orₗ Δ A B in_Δ => ⟨SplitCut.RuleApp.orₗ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .orᵣ Δ A B in_Δ => ⟨SplitCut.RuleApp.orᵣ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .boxₗ Δ A in_Δ => ⟨SplitCut.RuleApp.boxₗ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .boxᵣ Δ A in_Δ => ⟨SplitCut.RuleApp.boxᵣ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩

@[simp]
theorem ProofTranslation_f {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  SplitCut.f (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩) = CutPre.f (@CutPre.r _ _ _ _ (PartialProof y).α z_in_Cy) := by
    cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.f, CutPre.f]

@[simp]
theorem ProofTranslation_fₚ {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  SplitCut.fₚ (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩) = CutPre.fₚ (@CutPre.r _ _ _ _ (PartialProof y).α z_in_Cy) := by
    cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.fₚ, CutPre.fₚ]

@[simp]
theorem ProofTranslation_fₙ {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  SplitCut.fₙ (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩) = CutPre.fₙ (@CutPre.r _ _ _ _ (PartialProof y).α z_in_Cy) := by
    cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.fₙ_alternate, CutPre.fₙ_alternate]

theorem ProofTranslation_isBox {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩).isBox ↔ (CutPre.r (PartialProof y).α z_in_Cy).isBox := by
  cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.RuleApp.isBox, CutPre.RuleApp.isBox]

noncomputable def ProofTranslation {𝕏 : Proof} {σ}
(PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ)
  : SplitCut.Proof := by exact -- ∀ x : 𝕏.X, 𝕐 ⊢ leftInterpolant x
  { X := (y : 𝕏.X) × (PartialProof y).X
    α := ProofTranslationMap PartialProof
    h := by -- this is a lot of repetition! but I find that not using the intermediate 'ptm_eq' steps causes lean to oversimplify down to something harder to work from
          intro y_zy
          have h2 := (PartialProof y_zy.1).h y_zy.2
          cases r_def : (@CutPre.r _ _ _ _ (PartialProof y_zy.1).α y_zy.2) <;> simp [r_def, CutPre.fₙ_alternate] at h2
          case pre z _ =>
            have root_prop := (PartialProof z).root_prop
            have ptm_r_eq : SplitCut.r (ProofTranslationMap PartialProof) y_zy = SplitCut.RuleApp.skp (σ z) := by simp [SplitCut.r, ProofTranslationMap, r_def]
            have ptm_p_eq : SplitCut.p (ProofTranslationMap PartialProof) y_zy = [⟨z, (PartialProof z).root⟩] := by simp [SplitCut.p, ProofTranslationMap, r_def]
            simp [ptm_r_eq, ptm_p_eq, ProofTranslation_f]
            simp [SplitCut.f, root_prop]
          case cutₗ Δ φ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.cutₗ Δ φ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case cutᵣ Δ φ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.cutᵣ Δ φ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case wkₗ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.wkₗ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case wkᵣ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.wkᵣ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case topₗ Δ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.topₗ Δ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case topᵣ Δ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.topᵣ Δ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axₗₗ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axₗₗ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axₗᵣ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axₗᵣ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axᵣₗ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axᵣₗ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axᵣᵣ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axᵣᵣ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case orₗ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.orₗ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case orᵣ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.orᵣ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case andₗ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.andₗ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case andᵣ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.andᵣ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case boxₗ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.boxₗ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case boxᵣ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.boxᵣ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
    path := by
      intro ⟨y, z_y⟩ ⟨f, ⟨f_zero, f_succ⟩⟩ l
      -- infinite path in translation induces a path in the original proof

      by_cases ∃ (y : 𝕏.X), ∃ n, ∀ m ≥ n, (f m).1 = y
      case pos loop =>
        have ⟨y, n, n_prop⟩ := loop
        let g : ℕ → (PartialProof y).X := fun m ↦ (n_prop (m + n) (by simp)) ▸ (f (m + n)).2
        have ⟨n₂, n₂_prop⟩ := (PartialProof y).path ((n_prop n (by simp)) ▸ (f n).2) ⟨g, by sorry, by sorry⟩ l
        use n₂ + n
        unfold g at n₂_prop
        simp_all
        convert n₂_prop
        convert ProofTranslation_isBox PartialProof (f (l + n₂ + n)).fst (f (l + n₂ + n)).snd using 4
        · linarith
        · exact Eq.symm $ n_prop (l + n₂ + n) (by simp)
        · grind
      case neg path =>
        simp at path
        sorry

      -- let g : ℕ → {x : 𝕏.X // ∃ m, (f m).1 = x} := Nat.rec ⟨y, ⟨0, by simp [f_zero]⟩⟩ (fun n ⟨y, y_prop⟩ => by sorry)
      -- have g_prop : ∀ n, edge 𝕏.α (g n).1 (g (n + 1)).1 := by sorry
      -- have ⟨m, m_box⟩ := @inf_path_has_inf_boxes 𝕏 (fun n ↦ (g n).1) g_prop n
      -- if g (n + m) is Box then whatever g....

    }

noncomputable def InterpolantProofLeft' {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : SplitCut.Proof :=
  @ProofTranslation 𝕏 (@leftInterpolantSequent 𝕏 _) PartialInterpolationLeft

theorem InterpolantProofLeft_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
  : @InterpolantProofLeft' 𝕏 fin_X ⊢ leftInterpolantSequent x := by
  use ⟨x, (PartialInterpolationLeft x).root⟩
  rw [←(PartialInterpolationLeft x).root_prop]
  exact @ProofTranslation_f 𝕏 leftInterpolantSequent PartialInterpolationLeft x (PartialInterpolationLeft x).root
