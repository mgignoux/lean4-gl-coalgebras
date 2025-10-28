import GL.Logic
import GL.CoalgebraProof
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs

/- TRANSFORMATIONS -/

/-- Structure preserving map substituting Pₙ by C --/
def single (n : Nat) (C : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at k => if k == n then C else at k
  | na k => if k == n then ~ C else na k
  | A & B => (single n C A) & (single n C B)
  | A v B => (single n C A) v (single n C B)
  | □ A => □ (single n C A)
  | ◇ A => ◇ (single n C A)

/-- Structure preserving map substituting all atoms meeting a certain criteria p --/
def partial_ (p : Nat → Prop) [DecidablePred p] (σ : Subtype p → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : p n then σ ⟨n, h⟩ else at n
  | na n => if h : p n then ~ σ ⟨n, h⟩ else at n
  | A & B => (partial_ p σ A) & (partial_ p σ B)
  | A v B => (partial_ p σ A) v (partial_ p σ B)
  | □ A => □ (partial_ p σ A)
  | ◇ A => ◇ (partial_ p σ A)

/-- Structure preserving map substituting all atoms via a transformation σ --/
def full (σ : Nat → Formula) (A : Formula) : Formula := match A with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => σ n
  | na n => ~ (σ n)
  | A & B => (full σ A) & (full σ B)
  | A v B => (full σ A) v (full σ B)
  | □ A => □ (full σ A)
  | ◇ A => ◇ (full σ A)
termination_by Formula.size A
decreasing_by
  all_goals
  simp [Formula.size]
  try linarith

namespace split

def Proof.Sequent (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Sequent :=
  fin_X.elems.biUnion (fun x ↦ (f (r 𝕏.α x)).image (Sum.elim id id))

def Proof.freeVar (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Nat :=
  Sequent.freshVar (Proof.Sequent 𝕏)

noncomputable def encodeVar {𝕏 : Proof} [Fintype 𝕏.X] : 𝕏.X → Nat :=
  fun x ↦ 𝕏.freeVar + Fintype.equivFin 𝕏.X x

lemma encodeVar_inj (𝕏 : Proof) [Fintype 𝕏.X] : Function.Injective (@encodeVar 𝕏 _) := by
  simp [Function.Injective]
  intro x y hyp
  simp [encodeVar, Fin.val_eq_val] at hyp
  exact hyp

noncomputable def equation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Formula := match r : r 𝕏.α x with
  | RuleApp.topₗ _ _ => ⊥
  | RuleApp.topᵣ _ _ => ⊤
  | RuleApp.axₗₗ _ _ _ => ⊥
  | RuleApp.axₗᵣ _ k _ => na k
  | RuleApp.axᵣₗ _ k _ => at k
  | RuleApp.axᵣᵣ _ _ _ => ⊤
  | RuleApp.orₗ _ _ _ _ => match p_def : p 𝕏.α x with
    | [] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | [y] => at (encodeVar y)
    | y1 :: y2 :: ys => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
  | RuleApp.orᵣ _ _ _ _ => match p_def : p 𝕏.α x with
    | [] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | [y] => at (encodeVar y)
    | y1 :: y2 :: ys => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
  | RuleApp.andₗ _ _ _ _ => match p_def : p 𝕏.α x with
    | [] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | [y] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | y1 :: y2 :: [] => at (encodeVar y1) v at (encodeVar y2)
    | y1 :: y2 :: y3 :: ys => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
  | RuleApp.andᵣ _ _ _ _ => match p_def : p 𝕏.α x with
    | [] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | [y] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | y1 :: y2 :: [] => at (encodeVar y1) & at (encodeVar y2)
    | y1 :: y2 :: y3 :: ys => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
  | RuleApp.boxₗ _ _ _ => match p_def : p 𝕏.α x with
    | [] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | [y] => ◇ at (encodeVar y)
    | y1 :: y2 :: ys => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
  | RuleApp.boxᵣ _ _ _ => match p_def : p 𝕏.α x with
    | [] => by exfalso; have := 𝕏.h x; simp [r, p_def] at this
    | [y] => □ at (encodeVar y)
    | y1 :: y2 :: ys => by exfalso; have := 𝕏.h x; simp [r, p_def] at this

-- apply_substitution
noncomputable def extend {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (σ : 𝕏.X → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : 𝕏.freeVar ≤ n ∧ n < 𝕏.freeVar + fin_X.card then σ ((Fintype.equivFin 𝕏.X).symm ⟨n - 𝕏.freeVar, by omega⟩) else at n
  | na n => if h : 𝕏.freeVar ≤ n ∧ n < 𝕏.freeVar + fin_X.card then ~ σ ((Fintype.equivFin 𝕏.X).symm ⟨n - 𝕏.freeVar, by omega⟩) else na n
  | A & B => (extend σ A) & (extend σ B)
  | A v B => (extend σ A) v (extend σ B)
  | □ A => □ (extend σ A)
  | ◇ A => ◇ (extend σ A)

noncomputable def Solution_strong {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) : 𝕏.X → Formula
      -- ∀ y : {x : 𝕏.X // x ∈ Y},
      --     (χ y.val ≅ extend χ (equation y.val))
      --  ∧ (True) -- not a subformula property
      := by
  -- induction Y using Finset.induction_on --- DONT DO THIS, WE WANT TO SELECT THE ELEMENTS WE REMOVE
  by_cases Y = ∅
  case pos Y_em => -- if empty then vacuously done
    subst Y_em
    use fun x ↦ ⊤ -- give any function
    -- intro y
    -- exfalso
    -- simp_all only [Finset.empty_subset]
    -- obtain ⟨val, property⟩ := y
    -- simp_all only [Finset.notMem_empty]

  case neg Y_ne => -- if not empty then take an arbitrary element
    let y := Exists.choose $ @Finset.Nonempty.exists_mem _ Y (by by_contra h; simp at h; exact Y_ne h) -- must be smarter way to do this
    have := 𝕏.decidable
    by_cases Relation.TransGen (fun y1 y2 ↦ edge 𝕏.α y1 y2 ∧ (y1 ∈ Y ∧ y2 ∈ Y)) y y

    case pos h =>  -- if there is a loop then find the box node which must be in Y
      let z := Exists.choose $ exists_box_on_loop y (by sorry) -- property of h
      have z_in : z ∈ Y := by sorry -- this is not provable with the theorems now but is obvious

      have τ := Solution_strong (Y \ {z}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate

      sorry -- this is where we will need to use the FixedPointTheorem ....

    case neg => -- if there is no loop then find a leaf in ↑y

      have exists_leaf : ∃ l ∈ Y, (p 𝕏.α l).toFinset ∩ Y = ∅ := by sorry
      let leaf := Exists.choose $ exists_leaf

      -- maybe do cases (r α leaf) here to see what type of leaf it is, or prove if something is a leaf then

      have τ := Solution_strong (Y \ {leaf}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate

      use (single (encodeVar leaf) (equation leaf)) ∘ τ -- the composition

    --   intro y
    --   by_cases y.val = leaf
    --   case pos => sorry -- hard
    --   case neg ne =>
    --     have := τ_prop ⟨y, by aesop⟩

    --     simp
    --     have h : single (encodeVar leaf) (equation leaf) (τ ↑y) = (τ ↑y) := by sorry
    --     rw [h] -- introduce the cut coalgebras then we have transitivity of ≃
    -- --    simp [equation]
    --     have := 𝕏.h leaf
    --     cases rule : r 𝕏.α leaf <;> rw [rule] at this <;> sorry
    --     -- look at equation ↑y


termination_by Finset.card Y
decreasing_by
  · rw [←Finset.card_sdiff_add_card_inter Y {z}]
    cases value : (Y ∩ {z}).card -- roundabout method
    case zero h =>
      exfalso
      simp only [Finset.card_eq_zero, Finset.inter_singleton, z_in, ↓reduceIte, Finset.singleton_ne_empty] at value
    case succ => sorry --simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]
  · rw [←Finset.card_sdiff_add_card_inter Y {leaf}]
    cases value : (Y ∩ {leaf}).card -- roundabout method
    case zero h =>
      exfalso
      sorry
      -- simp only [Finset.card_eq_zero, Finset.inter_singleton, leaf_in_Y, ↓reduceIte, Finset.singleton_ne_empty] at value
    case succ => sorry -- simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]

theorem Solution_strong_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) :
      ∀ y : {x : 𝕏.X // x ∈ Y},
          (Solution_strong Y Y_sub y.val ≅ extend (Solution_strong Y Y_sub) (equation y.val)) := by sorry
      --  ∧ (True) -- not a subformula property



noncomputable def Interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : 𝕏.X → Formula
  := Solution_strong fin_X.elems (by simp)
      -- ∀ x : 𝕏.X, (σ x ≅ extend σ (equation x))
  --  ∧ ∀ x y : 𝕏.X, P y ∉ σ (P x)  -- how far can we get without this condition?

theorem Solution_prop (𝕏 : Proof) [fin_X : Fintype 𝕏.X] :
  ∀ x : 𝕏.X, (Interpolant x ≅ extend (@Interpolant 𝕏 _) (equation x)) := by
  have := Solution_strong_prop fin_X.elems (by simp)
  intro x
  exact this ⟨x, by sorry⟩

  --  ∧ ∀ x y : 𝕏.X, P y ∉ σ (P x)  -- how far can we get without this condition?

  -- := by
  -- have ⟨σ, σ_pf⟩ := existsSolution_strong 𝕏 fin_X.elems (by simp)
  -- use σ
  -- intro x
  -- simp at σ_pf
  -- exact σ_pf x (fin_X.complete x)

-- theorem existsSolution (𝕏 : Proof) [fin_X : Fintype 𝕏.X] :
--   ∃ σ : 𝕏.X → Formula,
--       ∀ x : 𝕏.X, (σ x ≅ extend σ (equation x))
--   --  ∧ ∀ x y : 𝕏.X, P y ∉ σ (P x)  -- how far can we get without this condition?
--   := by
--   have ⟨σ, σ_pf⟩ := existsSolution_strong fin_X.elems (by simp)
--   use σ
--   intro x
--   simp at σ_pf
--   exact σ_pf x (fin_X.complete x)


/- Defining Interpolants -/

end split
namespace CutPre

inductive RuleApp (P : List Sequent)
  | pre : (Δ : Finset Formula) → (Δ ∈ P) → RuleApp P
  | cut : (Δ : Finset Formula) → RuleApp P
  | wk : (Δ : Finset Formula) → (A : Formula) → (A ∈ Δ) → RuleApp P
  | skp : (Δ : Finset Formula) → RuleApp P
  | top : (Δ : Finset Formula) → ⊤ ∈ Δ → RuleApp P
  | ax : (Δ : Finset Formula) → (n : Nat) → (at n ∈ Δ ∧ na n ∈ Δ) → RuleApp P
  | and : (Δ : Finset Formula) → (A : Formula) → (B : Formula) → (A & B) ∈ Δ → RuleApp P
  | or : (Δ : Finset Formula) → (A : Formula) → (B : Formula) → (A v B) ∈ Δ → RuleApp P
  | box : (Δ : Finset Formula) → (A : Formula) → (□ A) ∈ Δ → RuleApp P

def fₚ {P : List Sequent} : RuleApp P → Finset Formula
  | RuleApp.pre Δ _ => Δ
  | RuleApp.cut _ => ∅
  | RuleApp.wk _ A _ => {A}
  | RuleApp.skp _ => {}
  | RuleApp.top _ _ => {⊤}
  | RuleApp.ax _ n _ => {at n, na n}
  | RuleApp.and _ A B _ => {A & B}
  | RuleApp.or _ A B _ => {A v B}
  | RuleApp.box _ A _ => {□ A}

def f {P : List Sequent} : RuleApp P → Finset Formula
  | RuleApp.pre Δ _ => Δ
  | RuleApp.cut Δ => Δ
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
    | RuleApp.cut _ => ∃ A : Formula, (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A}, (fₙ (r α x)) ∪ {~A}]
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


noncomputable def leftInterpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Sequent
  := {Interpolant x} ∪ Finset.filterMap Sum.getLeft? (f (r 𝕏.α x)) (by aesop) -- why is Finset.preimage noncomputable?

noncomputable def rightInterpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Sequent
  := {~(Interpolant x)} ∪ Finset.preimage (f (r 𝕏.α x)) Sum.inr (by aesop)


noncomputable def InterpolantProofFromPremisesLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : CutPre.CutProofFromPremises ((p 𝕏.α x).map leftInterpolant) := by
  cases rule : (r 𝕏.α x)  -- look at the interpolant form and proceed
  case topₗ Δ in_Δ =>
    exact {
      X := Unit
      α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by simp [leftInterpolant, rule, f, in_Δ]), {}⟩ -- : RuleApp × Finset Formula × Multiset X
      h := by aesop}
  case topᵣ Δ in_Δ =>
    exact {
      X := Unit
      α u := ⟨CutPre.RuleApp.top (leftInterpolant x) (by
        simp [leftInterpolant, Interpolant]
        left
        sorry
        ), {}⟩
      h := by aesop}
  all_goals
    sorry

noncomputable def InterpolantProofFromPremisesLeft_node {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : (InterpolantProofFromPremisesLeft x).X := by sorry


theorem InterpolantProofFromPremisesLeft_node_proves {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  @CutPre.f ((p 𝕏.α x).map leftInterpolant) (CutPre.r (InterpolantProofFromPremisesLeft x).α (InterpolantProofFromPremisesLeft_node x)) = (leftInterpolant x) := by sorry

noncomputable def InterpolantProofLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : CutPre.CutProofFromPremises [] :=
  -- construction of ∏ Cₓ from notes
  {
    X := (y : 𝕏.X) × (InterpolantProofFromPremisesLeft y).X
    α := by  -- change to match?
      intro ⟨y, z_y⟩
      -- have := r (InterpolantProofFromPremisesLeft y).α
      cases (@CutPre.r _ _ (InterpolantProofFromPremisesLeft y).α z_y)
      case pre Δ in_Δ => -- only interesting case
        exact ⟨CutPre.RuleApp.skp Δ, (p 𝕏.α y).map (fun x ↦ ⟨x, InterpolantProofFromPremisesLeft_node x⟩)⟩
      case cut Δ => exact ⟨CutPre.RuleApp.cut Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case wk Δ A in_Δ => exact ⟨CutPre.RuleApp.wk Δ A in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case skp Δ => exact ⟨CutPre.RuleApp.skp Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case top Δ in_Δ => exact ⟨CutPre.RuleApp.top Δ in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case ax Δ n in_Δ => exact ⟨CutPre.RuleApp.ax Δ n in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case and Δ A B in_Δ => exact ⟨CutPre.RuleApp.and Δ A B in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case or Δ A B in_Δ => exact ⟨CutPre.RuleApp.or Δ A B in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
      case box Δ A in_Δ => exact ⟨CutPre.RuleApp.box Δ A in_Δ, (CutPre.p (InterpolantProofFromPremisesLeft y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩

    h := by sorry}

theorem InterpolantProofLeft_provesInterpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : @InterpolantProofLeft 𝕏 _ ⊢ (leftInterpolant x) := by
  use ⟨x, InterpolantProofFromPremisesLeft_node x⟩
  rw [←InterpolantProofFromPremisesLeft_node_proves x]
  sorry
