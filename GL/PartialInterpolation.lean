import GL.Logic
import GL.CoalgebraProof
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Interpolants

namespace CutPre

inductive RuleApp {𝕏 : split.Proof} (x : 𝕏.X) (τ : 𝕏.X → Sequent)
  | pre : (y : 𝕏.X) → (y ∈ split.p 𝕏.α x) → RuleApp x τ
  | cut : (Δ : Sequent) → (A : Formula) → RuleApp x τ
  | wk : (Δ : Sequent) → (A : Formula) → A ∈ Δ → RuleApp x τ
  | top : (Δ : Sequent) → (⊤ ∈ Δ) → RuleApp x τ
  | ax : (Δ : Sequent) → (n : Nat) → (at n ∈ Δ ∧ na n ∈ Δ) → RuleApp x τ
  | and : (Δ : Sequent) → (A : Formula) → (B : Formula) → (A & B) ∈ Δ → RuleApp x τ
  | or : (Δ : Sequent) → (A : Formula) → (B : Formula) → (A v B) ∈ Δ → RuleApp x τ
  | box : (Δ : Sequent) → (A : Formula) → (□ A ∈ Δ) → RuleApp x τ


def fₚ {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} : RuleApp x τ → Sequent
  | RuleApp.pre y _ => τ y
  | RuleApp.cut _ _ => ∅
  | RuleApp.wk _ A _ => {A}
  | RuleApp.top _ _ => {⊤}
  | RuleApp.ax _ n _ => {at n, na n}
  | RuleApp.and _ A B _ => {A & B}
  | RuleApp.or _ A B _ => {A v B}
  | RuleApp.box _ A _ => {□ A}

def f {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} : RuleApp x τ → Sequent
  | RuleApp.pre y _ => τ y
  | RuleApp.cut Δ _ => Δ
  | RuleApp.wk Δ _ _ => Δ
  | RuleApp.top Δ _ => Δ
  | RuleApp.ax Δ _ _ => Δ
  | RuleApp.and Δ _ _ _ => Δ
  | RuleApp.or Δ _ _ _ => Δ
  | RuleApp.box Δ _ _ => Δ

def fₙ {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} : RuleApp x τ → Sequent := fun r ↦ f r \ fₚ r

universe u
@[simp] def T {𝕏 : split.Proof} (x : 𝕏.X) (τ : 𝕏.X → Sequent) : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨λ X ↦ ((RuleApp x τ × List X) : Type u), by rintro X Y f ⟨r, A⟩; exact ⟨r, A.map f⟩, by aesop_cat, by aesop_cat⟩

def r {X : Type u} {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} (α : X → (T x τ).obj X) (x : X) := (α x).1
def p {X : Type u} {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} (α : X → (T x τ).obj X) (x : X) := (α x).2
def edge  {X : Type u} {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} (α : X → (T x τ).obj X) (x y : X) : Prop := y ∈ p α x

structure CutProofFromPremises {𝕏 : split.Proof} (x : 𝕏.X) (τ : 𝕏.X → Sequent) where
  X : Type
  α : X → (T x τ).obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.pre _ _ => p α x = []
    | RuleApp.cut _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A}, (fₙ (r α x)) ∪ {~A}]
    | RuleApp.wk _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.top _ _ => p α x = []
    | RuleApp.ax _ _ _ => p α x = []
    | RuleApp.and _ A B _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A}, (fₙ (r α x)) ∪ {B}]
    | RuleApp.or _ A B _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A, B}]
    | RuleApp.box _ A _ => (p α x).map (fun x ↦ f (r α x)) = [Sequent.D (fₙ (r α x)) ∪ {A}]


def CutProofFromPremises.Proves {𝕏 : split.Proof} {x : 𝕏.X} {τ : 𝕏.X → Sequent} (𝕐 : CutProofFromPremises x τ) (Δ : Sequent) : Prop := ∃ x : 𝕐.X, f (r 𝕐.α x) = Δ
infixr:6 "⊢" => CutProofFromPremises.Proves

end CutPre

namespace split

@[simp]
noncomputable def SplitSequent.left (Δ : SplitSequent) : Sequent := Finset.filterMap Sum.getLeft? Δ (by aesop)
noncomputable def SplitSequent.right (Δ : SplitSequent) : Sequent := Finset.filterMap Sum.getRight? Δ (by aesop)

noncomputable def leftInterpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Sequent
  := {Interpolant 𝕏 (at (encodeVar x))} ∪ (f (r 𝕏.α x)).left -- why is Finset.preimage noncomputable?

/- PARTIAL INTERPOLANT PROOFS. I SPLIT THESE APART BECAUSE THEY RUN SO SLOW OTHERWISE -/
noncomputable def PartialLeft_topₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by simp [leftInterpolant, rule_def, f, in_Δ]), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_topᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by
      simp [leftInterpolant, eq, equation, rule_def] -- why not able to simpe with rule here
      left
      split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_axₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by simp [leftInterpolant, rule_def, f, in_Δ]), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_axₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by
      simp [leftInterpolant, f, in_Δ, eq, equation, rule_def]
      left
      split <;> simp_all only [Interpolant, and_true, Subtype.forall, Finset.mem_image, forall_exists_index, reduceCtorEq, partial_]
      split
      · exfalso
        sorry
      · simp_all
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_axᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by
      simp [leftInterpolant, f, in_Δ, eq, equation, rule_def]
      left
      split <;> simp_all only [Interpolant, and_true, Subtype.forall, Finset.mem_image, forall_exists_index, reduceCtorEq, partial_]
      split
      · exfalso
        sorry
      · simp_all
      ), {}⟩
    h := by intro u; simp [CutPre.r, CutPre.p]}
  else sorry

noncomputable def PartialLeft_axᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := Unit
    α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by
      simp [leftInterpolant, rule_def, f, eq, equation]
      left
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
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then
    match p_def : p 𝕏.α x with
      | [y] =>
        have 𝕏_h := 𝕏.h x
        have h : equation x = (at (encodeVar y) & at (encodeVar y)) := by
          simp [equation]
          split <;> simp_all
        { X := Fin 3
          α u :=
            match u with
            | 0 => ⟨CutPre.RuleApp.or (leftInterpolant x) φ ψ (by simp [leftInterpolant, rule_def, f, in_Δ]), [1]⟩
            | 1 => ⟨CutPre.RuleApp.and ((leftInterpolant x) \ {φ v ψ} ∪ {φ, ψ}) (Interpolant 𝕏 (at encodeVar y)) (Interpolant 𝕏 (at encodeVar y)) (by
              simp [Finset.mem_sdiff, leftInterpolant, eq, h]
              tauto), [2, 2]⟩
            | 2 => ⟨CutPre.RuleApp.pre y (by simp [p_def]), {}⟩
          h := by
            intro n
            match n with
              | 0 => simp only [CutPre.r, CutPre.p, CutPre.T, List.map_eq_singleton_iff, List.cons.injEq, and_true, exists_eq_left', CutPre.f, CutPre.fₙ, CutPre.fₚ, leftInterpolant, rule_def]
              | 1 =>
                simp [rule_def, p_def, -Finset.union_insert, -Finset.union_singleton, -Finset.singleton_union] at 𝕏_h
                simp only [fₙ_alternate] at 𝕏_h
                simp? [CutPre.r, CutPre.p, CutPre.r, CutPre.f, CutPre.fₙ, CutPre.fₚ, leftInterpolant, -Finset.union_insert, -Finset.union_singleton, -Finset.singleton_union, eq, h]
                sorry



              | 2 => sorry
          }
        | _ => sorry -- not possible
  else sorry

noncomputable def PartialLeft_orᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
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
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

noncomputable def PartialLeft_andᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

noncomputable def PartialLeft_boxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

noncomputable def PartialLeft_boxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then {
    X := sorry
    α u := sorry
    h := sorry
        }
  else sorry

set_option maxHeartbeats 500000
noncomputable def PartialLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises x (@leftInterpolant 𝕏 _) :=
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
/-
set_option maxHeartbeats 1000000
noncomputable def InterpolantProofFromPremisesLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises ((p 𝕏.α x).map leftInterpolant) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then match rule : (r 𝕏.α x) with
    | .topₗ Δ in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by simp [leftInterpolant, rule, f, in_Δ]), {}⟩ -- : RuleApp × Sequent × Multiset X
        h := by aesop}
    | .topᵣ Δ in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by
          simp [leftInterpolant, eq, equation, rule] -- why not able to simpe with rule here
          left
          split <;> simp_all [Interpolant, partial_] -- wow, do not forget about split!!!
          ), {}⟩
        h := by aesop}
    | .axₗₗ Δ n in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by simp [leftInterpolant, rule, f, in_Δ]), {}⟩ -- : RuleApp × Sequent × Multiset X
        h := by aesop}
    | .axₗᵣ Δ n in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by
          simp [leftInterpolant, f, in_Δ, eq, equation, rule]
          left
          split <;> simp_all only [Interpolant, and_true, Subtype.forall, Finset.mem_image, forall_exists_index, reduceCtorEq, partial_]
          split
          · exfalso
            sorry
          · simp_all
          ), {}⟩
        h := by aesop}
    | .axᵣₗ Δ n in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by
          simp [leftInterpolant, f, in_Δ, eq, equation, rule]
          left
          split <;> simp_all only [Interpolant, and_true, Subtype.forall, Finset.mem_image, forall_exists_index, reduceCtorEq, partial_]
          split
          · exfalso
            sorry
          · simp_all
          ), {}⟩
        h := by aesop}
    | .axᵣᵣ Δ n in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by
          simp [leftInterpolant, rule, f, eq, equation]
          left
          split <;> simp_all [Interpolant, partial_]
          ), {}⟩
        h := by aesop}
    | .orₗ Δ A B in_Δ => by
      have := 𝕏.h x
      simp only [rule, List.map_eq_singleton_iff] at this
      exact {
        X := Fin 2
        α u :=
          match u with
          | 0 => ⟨CutPre.RuleApp.or (leftInterpolant x) A B (by simp [leftInterpolant, rule, f, in_Δ]), [1]⟩
          | 1 => ⟨CutPre.RuleApp.pre (({Interpolant 𝕏 (at encodeVar x)} ∪ (f (RuleApp.orₗ Δ A B in_Δ)).left) \ {A v B} ∪ {A, B}) (by sorry), {}⟩
        h := by
          intro n
          match n with
            | 0 => simp only [CutPre.r, CutPre.p, List.map_singleton, CutPre.f, CutPre.fₙ, List.cons.injEq,
                   and_true, CutPre.fₚ, leftInterpolant, eq, equation] --List.getElem_map, leftInterpolant, and_true]
                   split <;> simp_all only [reduceCtorEq]
            | 1 => simp [CutPre.r, CutPre.p]
        }
    | .orᵣ Δ A B in_Δ => by
      have := 𝕏.h x
      simp only [rule, List.map_eq_singleton_iff] at this
      exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.pre (leftInterpolant x) (by sorry), {}⟩
        h := by simp [CutPre.r, CutPre.p]
        }
    | _ => sorry -- another Interpolant x = ... thing

  else by sorry -- same thing but with cut used first
-/


-- noncomputable def InterpolantProofFromPremisesLeft_node {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : (InterpolantProofFromPremisesLeft x).X := by sorry


-- noncomputable def InterpolantProofLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : CutPre.CutProofFromPremises [] := by exact --∀ x : 𝕏.X, 𝕐 ⊢ leftInterpolant x
--   {
--     X := (y : 𝕏.X) × (InterpolantProofFromPremisesLeft y).X
--     α :=  -- change to match?
--       fun ⟨y, z_y⟩ ↦
--       match (@CutPre.r _ _ (InterpolantProofFromPremisesLeft y).α z_y) with
--       | .pre Δ in_Δ => ⟨CutPre.RuleApp.skp Δ, (p 𝕏.α y).map (fun x ↦ ⟨x, InterpolantProofFromPremisesLeft_node x⟩)⟩ -- only interesting case
--       | .cut Δ A => ⟨CutPre.RuleApp.cut Δ A, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .wk Δ A in_Δ => ⟨CutPre.RuleApp.wk Δ A in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .skp Δ => ⟨CutPre.RuleApp.skp Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .top Δ in_Δ => ⟨CutPre.RuleApp.top Δ in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .ax Δ n in_Δ => ⟨CutPre.RuleApp.ax Δ n in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .and Δ A B in_Δ => ⟨CutPre.RuleApp.and Δ A B in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .or Δ A B in_Δ => ⟨CutPre.RuleApp.or Δ A B in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--       | .box Δ A in_Δ => ⟨CutPre.RuleApp.box Δ A in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
--     h := by
--       intro ⟨y, z_y⟩
--       simp [CutPre.r, CutPre.p]
--       split <;> split <;> simp_all -- reduce to 9 goals
--       · subst_eqs
--         have := (InterpolantProofFromPremisesLeft y).h z_y
--         simp_all [CutPre.r]
--       --  rw [←this]

--         sorry -- .cut case
--       all_goals
--         sorry
--   }
