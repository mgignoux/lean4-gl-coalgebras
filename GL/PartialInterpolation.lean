import GL.Logic
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Interpolants
import GL.SplitCutCoalgebraProof

namespace CutPre

inductive RuleApp {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent)
  | pre : (y : 𝕏.X) → (y ∈ Split.p 𝕏.α x) → RuleApp x τ
  | cut : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ -- might need a left and right later
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
  | RuleApp.pre y _ => τ y
  | RuleApp.cut _ _ => ∅
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
  | RuleApp.cut Δ _ => Δ
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
  | RuleApp.pre _ _ => ∅
  | RuleApp.cut Δ _ => Δ
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

structure CutProofFromPremises {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) where
  X : Type
  α : X → (T x τ).obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.pre _ _ => p α x = []
    | RuleApp.cut _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl $ ~A}]
    | RuleApp.wkₗ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.wkᵣ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.andₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inr A}]
    | _ => p α x = {}


def CutProofFromPremises.Proves {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (𝕐 : CutProofFromPremises x τ) (Δ : SplitSequent) : Prop := ∃ x : 𝕐.X, f (r 𝕐.α x) = Δ
infixr:6 "⊢" => CutProofFromPremises.Proves

end CutPre

namespace Split

@[simp]
noncomputable def SplitSequent.left  : SplitSequent → SplitSequent := @Finset.filter _ (fun | Sum.inl _ => true | Sum.inr _ => false) (by sorry)

@[simp]
noncomputable def SplitSequent.right : SplitSequent → SplitSequent := @Finset.filter _ (fun | Sum.inl _ => false | Sum.inr _ => true) (by sorry)

noncomputable def leftInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (Interpolant 𝕏 (at (encodeVar x)))} ∪ (SplitSequent.left (f (r 𝕏.α x)))

noncomputable def rightInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (Interpolant 𝕏 (at (encodeVar x))))} ∪ (SplitSequent.right (f (r 𝕏.α x)))

/- PARTIAL INTERPOLANT PROOFS. I SPLIT THESE APART BECAUSE THEY RUN SO SLOW OTHERWISE -/
noncomputable def PartialLeft_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.topₗ (leftInterpolantSequent x) (by simp [leftInterpolantSequent, rule_def, f, in_Δ]), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.topᵣ (leftInterpolantSequent x) (by
      simp [leftInterpolantSequent, eq, equation, rule_def] -- why not able to simpe with rule here
      split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.axₗₗ (leftInterpolantSequent x) n (by simp [leftInterpolantSequent, rule_def, f, in_Δ]), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
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
    h := by intro u; simp [CutPre.r, CutPre.p]}
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
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.topᵣ (leftInterpolantSequent x) (by
      simp [leftInterpolantSequent, rule_def, f, eq, equation]
      split <;> simp_all [Interpolant, partial_]
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
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
                simp [CutPre.r, CutPre.p]}
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
        h := by simp [CutPre.r, CutPre.p]}
      else sorry
        | _ => sorry

noncomputable def PartialLeft_andₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

noncomputable def PartialLeft_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

noncomputable def PartialLeft_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

noncomputable def PartialLeft_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolantSequent 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

set_option maxHeartbeats 500000 --PartialInterpolationLeft
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

set_option maxHeartbeats 20000000
noncomputable def InterpolantProofLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : SplitCut.Proof := by exact --∀ x : 𝕏.X, 𝕐 ⊢ leftInterpolant x
  { X := (y : 𝕏.X) × (PartialInterpolationLeft y).X
    α :=  -- change to match?
      fun ⟨y, z_y⟩ ↦
      match (@CutPre.r _ _ _ _ (PartialInterpolationLeft y).α z_y) with
      | .pre z z_in => ⟨SplitCut.RuleApp.skp (leftInterpolantSequent z), (p 𝕏.α y).map (fun x ↦ ⟨x, sorry⟩)⟩ -- map to the node
      | .cut Δ A => ⟨SplitCut.RuleApp.cut Δ A, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .wkₗ Δ A in_Δ => ⟨SplitCut.RuleApp.wkₗ Δ A in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .wkᵣ Δ A in_Δ => ⟨SplitCut.RuleApp.wkᵣ Δ A in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .topₗ Δ in_Δ => ⟨SplitCut.RuleApp.topₗ Δ in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .topᵣ Δ in_Δ => ⟨SplitCut.RuleApp.topᵣ Δ in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .axₗₗ Δ n in_Δ => ⟨SplitCut.RuleApp.axₗₗ Δ n in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .axₗᵣ Δ n in_Δ => ⟨SplitCut.RuleApp.axₗᵣ Δ n in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .axᵣₗ Δ n in_Δ => ⟨SplitCut.RuleApp.axᵣₗ Δ n in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .axᵣᵣ Δ n in_Δ => ⟨SplitCut.RuleApp.axᵣᵣ Δ n in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .andₗ Δ A B in_Δ => ⟨SplitCut.RuleApp.andₗ Δ A B in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .andᵣ Δ A B in_Δ => ⟨SplitCut.RuleApp.andᵣ Δ A B in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .orₗ Δ A B in_Δ => ⟨SplitCut.RuleApp.orₗ Δ A B in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .orᵣ Δ A B in_Δ => ⟨SplitCut.RuleApp.orᵣ Δ A B in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .boxₗ Δ A in_Δ => ⟨SplitCut.RuleApp.boxₗ Δ A in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .boxᵣ Δ A in_Δ => ⟨SplitCut.RuleApp.boxᵣ Δ A in_Δ, (CutPre.p (PartialInterpolationLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
    h := by
      intro y_zy
      have h1 := 𝕏.h y_zy.1
      have h2 := (PartialInterpolationLeft y_zy.1).h y_zy.2
      cases r_def : (@CutPre.r _ _ _ _ (PartialInterpolationLeft y_zy.1).α y_zy.2) <;> simp [r_def, CutPre.fₙ_alternate] at h2 <;> try simp [SplitCut.r, r_def, h2, SplitCut.fₙ_alternate, SplitCut.p]
      · sorry -- there is a sorry above so this is understandable
      · simp [←h2]
        intro a
        split <;> simp_all [SplitCut.f, CutPre.f]
      · have ⟨val, prop⟩ := h2
        refine ⟨val, prop.1, ?_⟩
        split <;> simp_all [SplitCut.f, CutPre.f]
      · have ⟨val, prop⟩ := h2
        refine ⟨val, prop.1, ?_⟩
        split <;> simp_all [SplitCut.f, CutPre.f]
      · simp [←h2]
        intro a
        split <;> simp_all [SplitCut.f, CutPre.f]
      · simp [←h2]
        intro a
        split <;> simp_all [SplitCut.f, CutPre.f]
      · have ⟨val, prop⟩ := h2
        refine ⟨val, prop.1, ?_⟩
        split <;> simp_all [SplitCut.f, CutPre.f]
      · have ⟨val, prop⟩ := h2
        refine ⟨val, prop.1, ?_⟩
        split <;> simp_all [SplitCut.f, CutPre.f]
      · have ⟨val, prop⟩ := h2
        refine ⟨val, prop.1, ?_⟩
        split <;> simp_all [SplitCut.f, CutPre.f]
      · have ⟨val, prop⟩ := h2
        refine ⟨val, prop.1, ?_⟩
        split <;> simp_all [SplitCut.f, CutPre.f]
    path := by sorry
  }
