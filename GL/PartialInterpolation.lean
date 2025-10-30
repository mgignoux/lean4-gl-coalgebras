import GL.Logic
import GL.CoalgebraProof
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Interpolants

namespace CutPre

inductive RuleApp (P : List Sequent)
  | pre : (Δ : Finset Formula) → (Δ ∈ P) → RuleApp P
  | cut : (Δ : Finset Formula) → (A : Formula) → RuleApp P
  | wk : (Δ : Finset Formula) → (A : Formula) → (A ∈ Δ) → RuleApp P
  | skp : (Δ : Finset Formula) → RuleApp P
  | top : (Δ : Finset Formula) → ⊤ ∈ Δ → RuleApp P
  | ax : (Δ : Finset Formula) → (n : Nat) → (at n ∈ Δ ∧ na n ∈ Δ) → RuleApp P
  | and : (Δ : Finset Formula) → (A : Formula) → (B : Formula) → (A & B) ∈ Δ → RuleApp P
  | or : (Δ : Finset Formula) → (A : Formula) → (B : Formula) → (A v B) ∈ Δ → RuleApp P
  | box : (Δ : Finset Formula) → (A : Formula) → (□ A) ∈ Δ → RuleApp P

def fₚ {P : List Sequent} : RuleApp P → Finset Formula
  | RuleApp.pre Δ _ => Δ
  | RuleApp.cut _ _ => ∅
  | RuleApp.wk _ A _ => {A}
  | RuleApp.skp _ => {}
  | RuleApp.top _ _ => {⊤}
  | RuleApp.ax _ n _ => {at n, na n}
  | RuleApp.and _ A B _ => {A & B}
  | RuleApp.or _ A B _ => {A v B}
  | RuleApp.box _ A _ => {□ A}

def f {P : List Sequent} : RuleApp P → Finset Formula
  | RuleApp.pre Δ _ => Δ
  | RuleApp.cut Δ _ => Δ
  | RuleApp.wk Δ _ _ => Δ
  | RuleApp.skp Δ => Δ
  | RuleApp.top Δ _ => Δ
  | RuleApp.ax Δ _ _ => Δ
  | RuleApp.and Δ _ _ _ => Δ
  | RuleApp.or Δ _ _ _ => Δ
  | RuleApp.box Δ _ _ => Δ

def fₙ {P : List Sequent} : RuleApp P → Finset Formula := fun r ↦ f r \ fₚ r

universe u
@[simp] def T (P : List Sequent) : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨⟨λ X ↦ ((RuleApp P × List X) : Type u), by rintro X Y f ⟨r, A⟩; exact ⟨r, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩

def r {X : Type u} {P : List Sequent} (α : X → (T P).obj X) (x : X) := (α x).1
def p {X : Type u} {P : List Sequent} (α : X → (T P).obj X) (x : X) := (α x).2
def edge  {X : Type u} {P : List Sequent} (α : X → (T P).obj X) (x y : X) : Prop := y ∈ p α x

structure CutProofFromPremises (P : List Sequent) where
  X : Type
  α : X → (T P).obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.pre _ _ => p α x = []
    | RuleApp.cut _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A}, (fₙ (r α x)) ∪ {~A}]
    | RuleApp.wk _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.skp _ => (p α x).map (fun x ↦ f (r α x)) = [f (r α x)]
    | RuleApp.top _ _ => p α x = []
    | RuleApp.ax _ _ _ => p α x = []
    | RuleApp.and _ A B _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A}, (fₙ (r α x)) ∪ {B}]
    | RuleApp.or _ A B _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A, B}]
    | RuleApp.box _ A _ => (p α x).map (fun x ↦ f (r α x)) = [D (fₙ (r α x)) ∪ {A}]


def CutProofFromPremises.Proves {P : List Sequent} (𝕏 : CutProofFromPremises P) (Δ : Finset Formula) : Prop := ∃ x : 𝕏.X, f (r 𝕏.α x) = Δ
infixr:6 "⊢" => CutProofFromPremises.Proves

end CutPre

namespace split

@[simp]
noncomputable def SplitSequent.left (Δ : SplitSequent) : Sequent := Finset.filterMap Sum.getLeft? Δ (by aesop)

noncomputable def leftInterpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Sequent
  := {Interpolant 𝕏 (at (encodeVar x))} ∪ (f (r 𝕏.α x)).left -- why is Finset.preimage noncomputable?


set_option maxHeartbeats 1000000
noncomputable def InterpolantProofFromPremisesLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises ((p 𝕏.α x).map leftInterpolant) :=
  if eq : Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) then match rule : (r 𝕏.α x) with
    | .topₗ Δ in_Δ => by exact {
        X := Unit
        α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by simp [leftInterpolant, rule, f, in_Δ]), {}⟩ -- : RuleApp × Finset Formula × Multiset X
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
        α u := ⟨CutPre.RuleApp.ax (leftInterpolant x) n (by simp [leftInterpolant, rule, f, in_Δ]), {}⟩ -- : RuleApp × Finset Formula × Multiset X
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

noncomputable def InterpolantProofFromPremisesLeft_node {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : (InterpolantProofFromPremisesLeft x).X := by sorry


noncomputable def InterpolantProofLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : CutPre.CutProofFromPremises [] := by exact --∀ x : 𝕏.X, 𝕐 ⊢ leftInterpolant x
  {
    X := (y : 𝕏.X) × (InterpolantProofFromPremisesLeft y).X
    α :=  -- change to match?
      fun ⟨y, z_y⟩ ↦
      match (@CutPre.r _ _ (InterpolantProofFromPremisesLeft y).α z_y) with
      | .pre Δ in_Δ => ⟨CutPre.RuleApp.skp Δ, (p 𝕏.α y).map (fun x ↦ ⟨x, InterpolantProofFromPremisesLeft_node x⟩)⟩ -- only interesting case
      | .cut Δ A => ⟨CutPre.RuleApp.cut Δ A, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .wk Δ A in_Δ => ⟨CutPre.RuleApp.wk Δ A in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .skp Δ => ⟨CutPre.RuleApp.skp Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .top Δ in_Δ => ⟨CutPre.RuleApp.top Δ in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .ax Δ n in_Δ => ⟨CutPre.RuleApp.ax Δ n in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .and Δ A B in_Δ => ⟨CutPre.RuleApp.and Δ A B in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .or Δ A B in_Δ => ⟨CutPre.RuleApp.or Δ A B in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      | .box Δ A in_Δ => ⟨CutPre.RuleApp.box Δ A in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
    h := by
      intro ⟨y, z_y⟩
      simp [CutPre.r, CutPre.p]
      split <;> split <;> simp_all -- reduce to 9 goals
      · subst_eqs
        have := (InterpolantProofFromPremisesLeft y).h z_y
        simp_all [CutPre.r]
      --  rw [←this]

        sorry -- .cut case
      all_goals
        sorry
  }
