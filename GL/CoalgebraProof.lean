import GL.Logic
import Mathlib.Data.Set.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Finset.Lattice.Basic


instance {α} [DecidableEq α] (Γ : Finset α) : Union {x // x ∈ Γ.powerset} where -- mathlib ????
  union A B := ⟨A ∪ B, by
    apply Finset.mem_powerset.2
    apply Finset.subset_iff.2
    intro x h
    rcases (Finset.mem_union.1 h) with h | h
    · apply Finset.mem_of_subset (Finset.mem_powerset.1 A.2) h
    · apply Finset.mem_of_subset (Finset.mem_powerset.1 B.2) h
    ⟩

universe u

inductive RuleApp
  | top : (Δ : Finset Formula) → ⊤ ∈ Δ → RuleApp
  | ax : (Δ : Finset Formula) → (n : Nat) → (at n ∈ Δ ∧ na n ∈ Δ) → RuleApp
  | and : (Δ : Finset Formula) → (A : Formula) → (B : Formula) → (A & B) ∈ Δ → RuleApp
  | or : (Δ : Finset Formula) → (A : Formula) → (B : Formula) → (A v B) ∈ Δ → RuleApp
  | box : (Δ : Finset Formula) → (A : Formula) → (□ A) ∈ Δ → RuleApp

@[simp] def T : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨⟨λ X ↦ ((RuleApp × List X) : Type u), by rintro X Y f ⟨r, A⟩; exact ⟨r, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩

def D (Γ : Sequent) : Sequent := Finset.filter Formula.isDiamond Γ ∪ Finset.filterMap Formula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  cases A <;> cases B
  all_goals
  simp_all [Formula.opUnDi])

def fₚ : RuleApp → Finset Formula
  | RuleApp.top _ _ => {⊤}
  | RuleApp.ax _ n _ => {at n, na n}
  | RuleApp.and _ A B _ => {A & B}
  | RuleApp.or _ A B _ => {A v B}
  | RuleApp.box _ A _ => {□ A}

def f : RuleApp → Finset Formula
  | RuleApp.top Δ _ => Δ
  | RuleApp.ax Δ _ _ => Δ
  | RuleApp.and Δ _ _ _ => Δ
  | RuleApp.or Δ _ _ _ => Δ
  | RuleApp.box Δ _ _ => Δ

def fₙ : RuleApp → Finset Formula := fun r ↦ f r \ fₚ r

theorem fₙ_alternate (r : RuleApp) : fₙ r = match r with
  | RuleApp.top Δ _ => Δ \ {⊤}
  | RuleApp.ax Δ n _ => Δ \ {at n, na n}
  | RuleApp.and Δ A B _ => Δ \ {A & B}
  | RuleApp.or Δ A B _ => Δ \ {A v B}
  | RuleApp.box Δ A _ => Δ \ {□ A} := by cases r <;> simp [fₙ, f, fₚ]

theorem fₚ_sub_f {r : RuleApp} : fₚ r ⊆ f r := by
  cases r <;> simp_all [fₚ, f]
  · simp_all [Finset.subset_iff, Finset.mem_insert]

theorem fₙ_sub_f {r : RuleApp} : fₙ r ⊆ f r := by
  cases r <;> simp_all [fₙ, f]

def isBox : RuleApp → Prop
  | RuleApp.box _ _ _ => True
  | _ => False

def r {X : Type u} (α : X → T.obj X) (x : X) := (α x).1
def p {X : Type u} (α : X → T.obj X) (x : X) := (α x).2
def edge  {X : Type u} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

structure Proof where
  X : Type
  α : X → T.obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.top _ _ => p α x = []
    | RuleApp.ax _ _ _ => p α x = []
    | RuleApp.and _ A B _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A}, (fₙ (r α x)) ∪ {B}]
    | RuleApp.or _ A B _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {A, B}]
    | RuleApp.box _ A _ => (p α x).map (fun x ↦ f (r α x)) = [D (fₙ (r α x)) ∪ {A}]

instance (𝕏 : Proof) : CategoryTheory.Endofunctor.Coalgebra T where
  V := 𝕏.X
  str := 𝕏.α

/- LEMMAS -/

theorem edge_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : (edge 𝕏.α) x y) : f (r 𝕏.α y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  unfold edge at x_y
  have := 𝕏.h x
  cases rule : r 𝕏.α x <;> simp only [rule] at this
  · exfalso; simp_all
  · exfalso; simp_all
  case and Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_cons, List.not_mem_nil, or_false] at x_y
    rcases x_y with h|h <;> rw [h]
    · simp only [Sequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      intro χ χ_cases
      rcases χ_cases with h|_ <;> subst_eqs
      · exact ⟨χ, fₙ_sub_f h, Formula.FL_refl⟩
      · exact ⟨φ & ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
    · simp only [Sequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      intro χ χ_cases
      rcases χ_cases with h|_ <;> subst_eqs
      · exact ⟨χ, fₙ_sub_f h, Formula.FL_refl⟩
      · exact ⟨φ & ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
  case or Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Finset.union_insert, Sequent.FL, Finset.subset_iff, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with _|h|_ <;> subst_eqs
    · exact ⟨φ v ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, Formula.FL_refl⟩
    · exact ⟨φ v ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
  case box Δ φ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Sequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with h|_ <;> subst_eqs
    · simp [D] at h
      rcases h with ⟨h,_⟩|⟨θ,h1,h2⟩
      · refine ⟨χ, fₙ_sub_f h, by simp [Formula.FL_refl]⟩
      · refine ⟨◇χ, ?_, by simp [Formula.FL, Formula.FL_refl]⟩
        cases θ <;> simp [Formula.opUnDi] at h2
        subst h2
        exact fₙ_sub_f h1
    · exact ⟨□ φ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩

theorem path_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y) : f (r 𝕏.α y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  induction x_y
  case refl => exact Sequent.FL_refl
  case tail y z x_y y_z fy_fx =>
    apply Finset.Subset.trans (edge_in_FL y_z)
    apply Sequent.FL_subset at fy_fx
    simp only [Sequent.FL_idem] at fy_fx
    exact fy_fx

/- POINT GENERATION -/

@[simp] def α_point (𝕐 : Proof) (x : 𝕐.X) : {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} → T.obj {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} :=
  fun y ↦ ⟨(𝕐.α y.1).1,
          List.pmap (fun x y ↦ ⟨x, y⟩) (𝕐.α y.1).2 (fun _ z_in ↦ Relation.ReflTransGen.tail y.2 z_in)⟩

def PointGeneratedProof (𝕐 : Proof) (x : 𝕐.X) : Proof where
  X := {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y }
  α := α_point 𝕐 x
  h := by
    intro ⟨y, y_in⟩
    have h := 𝕐.h y
    simp_all only [r, α_point]
    cases r_def : (𝕐.α y).1 <;> simp_all only [p, α_point, List.pmap, List.map_pmap, List.pmap_eq_map]

lemma node_in_pg_sequent_in_FL (𝕏 : Proof) (x : 𝕏.X) : ∀ y : (PointGeneratedProof 𝕏 x).X, f (r (α_point 𝕏 x) y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  simp [PointGeneratedProof, r]
  intro y x_y
  exact path_in_FL x_y

/- FILTRATIONS -/

instance instSetoidX (𝕏 : Proof) : Setoid 𝕏.X where
  r x y := f (r 𝕏.α x) = f (r 𝕏.α y)
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot 𝕐 (x : Quotient (instSetoidX 𝕐)) :=
  T.map (Quotient.mk (instSetoidX 𝕐)) (𝕐.α (Quotient.out x))

noncomputable def Filtration (𝕐 : Proof) : Proof where
  X := Quotient (instSetoidX 𝕐)
  -- x := ⟦𝕐.x⟧
  α := α_quot 𝕐
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidX 𝕐) x
      have h := 𝕐.h (@Quotient.out _ (instSetoidX 𝕐) ⟦x⟧)
      simp only [r,p,α_quot,T] at *
      convert h -- wow
      · simp only [List.map_eq_nil_iff]
      · simp only [List.map_eq_nil_iff]
      · simp only [List.map_map, List.map_inj_left, Function.comp_apply]
        intro a a_in
        exact hyp a
      · simp only [List.map_map, List.map_inj_left, Function.comp_apply]
        intro a a_in
        exact hyp a
      · simp only [List.map_map, List.map_inj_left, Function.comp_apply]
        intro a a_in
        exact hyp a

/- SMALL MODEL PROPERTY -/

def Proof.Proves (𝕏 : Proof) (Δ : Finset Formula) : Prop := ∃ x : 𝕏.X, f (r 𝕏.α x) = Δ
infixr:6 "⊢" => Proof.Proves

theorem finite_proof_of_proof (𝕏 : Proof) (Δ : Sequent) : (𝕏 ⊢ Δ) → ∃ 𝕐, Finite 𝕐.X ∧ (𝕐 ⊢ Δ) := by -- ask malvin
  intro X_proves_Δ
  have ⟨x, f_Δ⟩ := X_proves_Δ
  use PointGeneratedProof (Filtration 𝕏) (Quotient.mk (instSetoidX 𝕏) x)
  constructor
  -- · refine ⟨?_, by simp⟩ -- just to get rid of the true thing
  · have h : Finite (Sequent.FL Δ).powerset := by
      apply Set.finite_coe_iff.1
      apply Finset.finite_toSet
    apply @Finite.of_injective _ _ h (fun y ↦ ⟨f (r ((PointGeneratedProof (Filtration 𝕏) ⟦x⟧).α) y), by
      simp only [Finset.mem_powerset]
      have in_fl := node_in_pg_sequent_in_FL (Filtration 𝕏) ⟦x⟧ y
      convert in_fl
      simp [←f_Δ, Filtration, r]
      exact Eq.symm $ Quotient.mk_out x⟩)
    simp [Function.Injective]
    intro z1 z2 f_z_eq
    simp [PointGeneratedProof, Filtration, r] at f_z_eq
    apply Subtype.eq
    apply Quotient.out_equiv_out.1
    exact f_z_eq
  · use ⟨Quotient.mk (instSetoidX 𝕏) x, Relation.ReflTransGen.refl⟩
    rw [←f_Δ]
    simp [r, Filtration, PointGeneratedProof]
    exact Quotient.mk_out x

/- THEOREMS ABOUT LOOPS -/

theorem loop_has_box_app (𝕏 : Proof) (x : 𝕏.X) :
  (Relation.TransGen (edge 𝕏.α)) x x →
    ∃ (y : 𝕏.X), (Relation.ReflTransGen (edge 𝕏.α)) x y
      ∧ (Relation.ReflTransGen (edge 𝕏.α)) y x
      ∧ isBox (r 𝕏.α y) := by
  intro x_x
  cases x_x
  case single xex => sorry
  case tail => sorry


/- ADMISSIBILITY -/

def equiv (A : Formula) (B : Formula) : Prop :=
  (∃ (𝕏 : Proof), 𝕏 ⊢ {~A, B}) ∧ (∃ (𝕏 : Proof), 𝕏 ⊢ {A, ~B})
infixr:7 "≅" => equiv

theorem not_prove_empty : ¬ ∃ 𝕏, 𝕏 ⊢ {} := by
  by_contra con
  have ⟨𝕏, x, x_em⟩ := con
  cases rule : r 𝕏.α x <;> simp_all [f, r] <;> aesop

lemma hm {a b c : ℕ} : b ≤ a → (c < b) → (a - b) + c < a := by grind only [cases Or]

lemma form_in_seq_size_le {A : Formula} {Δ : Sequent} : A ∈ Δ → A.size ≤ Δ.size := by
  intro A_in
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 A_in) (by simp) : A.size ≤ Δ.size)
  -- have h : Δ = Δ \ {A} ∪ {A} := by sorry
  -- rw [h]
  -- simp [Sequent.size, Finset]

theorem and_subproofs_left (𝕏 : Proof) (x : 𝕏.X) (A B : Formula) (Δ : Finset Formula) (AB_in : (A & B) ∈ Δ)(h : r 𝕏.α x = RuleApp.and Δ A B AB_in) : 𝕏 ⊢ Δ \ {A & B} ∪ {A} := by
  have := 𝕏.h x
  simp [h] at this
  have := congr_arg List.length this
  simp [] at this
  exact match p_def : p 𝕏.α x with
    | [] => by exfalso; simp [p_def] at this
    | [y] => by exfalso; simp [p_def] at this
    | [y,z] => by
      simp_all
      use y
      have := this.1
      simp [this]
      cases (r 𝕏.α y) <;> simp [fₙ, f, fₚ]
    | y :: z :: x :: xs => by exfalso; simp [p_def] at this

theorem and_subproofs_right (𝕏 : Proof) (x : 𝕏.X) (A B : Formula) (Δ : Finset Formula) (AB_in : (A & B) ∈ Δ)(h : r 𝕏.α x = RuleApp.and Δ A B AB_in) : 𝕏 ⊢ Δ \ {A & B} ∪ {B} := by
  have := 𝕏.h x
  simp [h] at this
  have := congr_arg List.length this
  simp [] at this
  exact match p_def : p 𝕏.α x with
    | [] => by exfalso; simp [p_def] at this
    | [y] => by exfalso; simp [p_def] at this
    | [y,z] => by
      simp_all
      use z
      have := this.2
      simp [this]
      cases (r 𝕏.α y) <;> simp [fₙ, f, fₚ]
    | y :: z :: x :: xs => by exfalso; simp [p_def] at this

theorem box_subproof (𝕏 : Proof) (x : 𝕏.X) (A : Formula) (Δ : Finset Formula) (A_in : □ A ∈ Δ) (h : r 𝕏.α x = RuleApp.box Δ A A_in) : 𝕏 ⊢ D (Δ \ {□ A}) ∪ {A} := by
  have := 𝕏.h x
  simp only [h] at this
  have := congr_arg List.length this
  simp at this
  exact match p_def : p 𝕏.α x with
    | [] => by exfalso; simp [p_def] at this
    | [y] => by
        simp_all
        use y
        simp [this]
        cases (r 𝕏.α y) <;> simp [fₙ, f, fₚ]
    | [y,z] => by exfalso; simp [p_def] at this
    | y :: z :: x :: xs => by exfalso; simp [p_def] at this

theorem weakening_helper {Γ : Finset Formula} {A B D : Formula} (A_ne : D ≠ A) :  Γ \ {D} ∪ ({B} ∪ {A}) = (Γ ∪ {A}) \ {D} ∪ {B} := by
  simp [Finset.union_sdiff_distrib]
  have h1 : {A} \ {D} = ({A} : Finset Formula) := by simp_all;
  have h2 : {A} ∪ {B} = {B} ∪ ({A} : Finset Formula) := by simp [Finset.union_comm]
  simp [h1, h2]

lemma Sequent.D_size_wod_leq_size_wod (Γ : Sequent) : (D Γ).size_without_diamond ≤ Γ.size_without_diamond := by
  induction Γ using Finset.induction
  case empty => simp [D]
  case insert A Δ A_ni ih =>
    have dis : Disjoint {A} Δ := Finset.disjoint_singleton_left.2 A_ni
    simp only [Finset.insert_eq, size_wod_disjoint dis]
    sorry -- very doable just annoying

theorem weakening (A : Formula) (Δ : Finset Formula) : (∃ 𝕏, 𝕏 ⊢ Δ) → (∃ 𝕏, 𝕏 ⊢ Δ ∪ {A}) := by
  intro ⟨𝕏, x, x_Δ⟩
  by_cases A ∈ Δ
  case pos A_in => refine ⟨𝕏, x, by simp [x_Δ, A_in]⟩
  case neg A_ni =>
    cases rule : r 𝕏.α x
    case top Γ top_in =>
      use {
        X := Unit
        α y := ⟨RuleApp.top (Γ ∪ {A}) (by simp_all) , {}⟩--by simp_all only [f, Finset.mem_union]; left; subst x_Δ; exact top_in), {}⟩ -- : RuleApp × Finset Formula × Multiset X
        h := by aesop}
      use ()
      simp [f, r]
      aesop
    case ax Γ n lem_in =>
      use {
        X := Unit
        α y := ⟨RuleApp.ax (Γ ∪ {A}) n (by simp_all) , {}⟩--by simp_all only [f, Finset.mem_union]; left; subst x_Δ; exact top_in), {}⟩ -- : RuleApp × Finset Formula × Multiset X
        h := by aesop}
      use ()
      simp [f, r]
      aesop
    case and Γ B C and_in =>
      simp only [f, rule] at x_Δ
      subst x_Δ
      have for_term1 : Sequent.size_without_diamond ((fₙ (r 𝕏.α x)) ∪ {B}) < Sequent.size_without_diamond Γ := by
        calc
          _ ≤ Sequent.size_without_diamond Γ - (B & C).size + B.size := by
            simp [fₙ, f, rule, fₚ]
            by_cases Disjoint (Γ \ {B & C}) {B}
            case pos dis =>
              simp only [Sequent.size_wod_disjoint dis]
              simp [Sequent.size_wod_sdiff (Finset.singleton_subset_iff.2 and_in)]
              have h : Sequent.size_without_diamond {B&C} = (B&C).size := by
                simp [Sequent.size_without_diamond]
                rw [Finset.filter_singleton (λ (A : Formula) ↦ ¬ A.isDiamond) (B&C)]
                simp [Formula.isDiamond]
              simp [h]
              cases B
              all_goals
                simp [Sequent.size_without_diamond]
                rw [Finset.filter_singleton (λ (A : Formula) ↦ ¬ A.isDiamond) _]
                simp [Formula.isDiamond]
            case neg ndi =>
              have h : (Γ \ {B&C}) ∪ {B} = (Γ \ {B&C}) := by
                simp [Finset.union_eq_left]
                simp_all
              simp [h]
              simp only [Sequent.size_wod_sdiff (Finset.singleton_subset_iff.2 and_in)]
              have h : Sequent.size_without_diamond {B&C} = (B&C).size := by
                simp [Sequent.size_without_diamond]
                rw [Finset.filter_singleton (λ (A : Formula) ↦ ¬ A.isDiamond) (B&C)]
                simp [Formula.isDiamond]
              simp [h]
          _ < Sequent.size_without_diamond Γ := by
            apply hm
            · exact form_in_seq_size_le (Finset.mem_filter.2 ⟨and_in, by simp [Formula.isDiamond]⟩)
            · simp [Formula.size]; linarith
      have for_term2 : Sequent.size_without_diamond ((fₙ (r 𝕏.α x)) ∪ {C}) < Sequent.size_without_diamond Γ := by
        calc
          _ ≤ Sequent.size_without_diamond Γ - (B & C).size + C.size := by
            simp [fₙ, f, rule, fₚ]
            by_cases Disjoint (Γ \ {B & C}) {C}
            case pos dis =>
              have := Sequent.size_wod_disjoint dis
              simp [Sequent.size_wod_disjoint dis]
              simp [Sequent.size_wod_sdiff (Finset.singleton_subset_iff.2 and_in)]
              have h : Sequent.size_without_diamond {B&C} = (B&C).size := by
                simp [Sequent.size_without_diamond]
                rw [Finset.filter_singleton (λ (A : Formula) ↦ ¬ A.isDiamond) (B&C)]
                simp [Formula.isDiamond]
              simp [h]
              cases C
              all_goals
                simp [Sequent.size_without_diamond]
                rw [Finset.filter_singleton (λ (A : Formula) ↦ ¬ A.isDiamond) _]
                simp [Formula.isDiamond]
            case neg ndi =>
              have h : (Γ \ {B&C}) ∪ {C} = (Γ \ {B&C}) := by
                simp [Finset.union_eq_left]
                simp_all
              simp [h]
              simp only [Sequent.size_wod_sdiff (Finset.singleton_subset_iff.2 and_in)]
              have h : Sequent.size_without_diamond {B&C} = (B&C).size := by
                simp [Sequent.size_without_diamond]
                rw [Finset.filter_singleton (λ (A : Formula) ↦ ¬ A.isDiamond) (B&C)]
                simp [Formula.isDiamond]
              simp [h]
          _ < Sequent.size_without_diamond Γ := by
            apply hm
            · exact form_in_seq_size_le (Finset.mem_filter.2 ⟨and_in, by simp [Formula.isDiamond]⟩)
            · simp [Formula.size]; linarith
      have ⟨𝕐l, yl, pfl⟩ := weakening A ((fₙ (r 𝕏.α x)) ∪ {B}) (by use 𝕏; convert (and_subproofs_left 𝕏 x B C Γ and_in rule); simp [fₙ, rule, f, fₚ]) -- put in seperate theorem
      have ⟨𝕐r, yr, pfr⟩ := weakening A ((fₙ (r 𝕏.α x)) ∪ {C}) (by use 𝕏; convert (and_subproofs_right 𝕏 x B C Γ and_in rule); simp [fₙ, rule, f, fₚ]) -- put in seperate theorem)
      clear for_term1 for_term2
      use {
        X := 𝕐l.X ⊕ 𝕐r.X ⊕ Unit
        α
        | Sum.inl x => T.map (Sum.inl) (𝕐l.α x)
        | Sum.inr (Sum.inl x) => T.map (Sum.inr ∘ Sum.inl) (𝕐r.α x)
        | Sum.inr (Sum.inr z) => ⟨RuleApp.and (Γ ∪ {A}) B C (by simp_all), [Sum.inl yl, Sum.inr $ Sum.inl yr]⟩
        h := by
          intro x
          rcases x with x1 | x2 | x3
          · simp [r]
            have := 𝕐l.h x1
            cases r_def : (𝕐l.α x1).1 <;> simp_all [r, p]
            · convert this
          · simp [r]
            have := 𝕐r.h x2
            cases r_def : (𝕐r.α x2).1 <;> simp_all [r, p]
            · convert this
          · simp_all only [r]
            simp [p, pfl, pfr]
            cases r_defl : (𝕐l.α yl).1 <;> cases r_defr : (𝕐r.α yr).1 <;> simp only [fₙ_alternate]
            all_goals
              constructor
              all_goals
                apply weakening_helper
                intro con
                apply A_ni
                rw [con] at and_in
                exact and_in}
      use Sum.inr (Sum.inr ())
      simp [f, r]
    case or => sorry
    case box Γ C box_in =>
      simp only [f, rule] at x_Δ
      subst x_Δ --heres where we do cases on A
      by_cases A.isDiamond
      case pos A_di =>
        cases A <;> simp [Formula.isDiamond] at A_di
        case diamond B =>
          have ⟨𝕐, y, pf⟩ := weakening B (D (fₙ (r 𝕏.α x)) ∪ {C, ◇ B}) (by
            have for_termination : Sequent.size_without_diamond (D (fₙ (r 𝕏.α x)) ∪ {C}) < Sequent.size_without_diamond (f (r 𝕏.α x)) := by
              calc
                _ ≤ Sequent.size_without_diamond ((fₙ (r 𝕏.α x)) ∪ {C}) := by
                  have := Sequent.D_size_wod_leq_size_wod (fₙ (r 𝕏.α x))
                  sorry

                _ < Sequent.size_without_diamond (f (r 𝕏.α x)) := by
                  simp [rule, f, fₙ_alternate]
                  sorry
            have ⟨𝕐, y, pf⟩ := weakening (◇ B) (D (fₙ (r 𝕏.α x)) ∪ {C}) (by use 𝕏; convert (box_subproof 𝕏 x C Γ box_in rule); simp [fₙ, rule, f, fₚ]) -- put in seperate theorem
            clear for_termination
            refine ⟨𝕐, y, ?_⟩
            · have h : ({C} : Finset Formula) ∪ {◇ B} = {C, ◇ B} := by aesop
              simp only [pf, ←h, Finset.union_assoc])
          use {
            X := 𝕐.X ⊕ Unit
            α
            | Sum.inl x => T.map (Sum.inl) (𝕐.α x)
            | Sum.inr z => ⟨RuleApp.box (Γ ∪ {◇ B}) C (by simp_all), [Sum.inl y]⟩
            h := by
              intro x
              rcases x with x1 | x2
              · simp [r]
                have := 𝕐.h x1
                cases r_def : (𝕐.α x1).1 <;> simp_all [r, p]
                · convert this
              · simp_all only [r]
                simp only [T, p, List.map, pf, List.cons.injEq, and_true, fₙ_alternate]
                apply Finset.ext
                intro E
                simp [D]
                constructor
                · aesop
                · intro mpp
                  rcases mpp with ⟨⟨c1, c2⟩, c3⟩ | ⟨c1, ⟨c2, c3⟩, c4⟩ | c
                  · rcases c1 with c1 | c1
                    · exact Or.inr (Or.inl ⟨⟨c1, c2⟩, c3⟩)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl c1)))
                  · rcases c2 with c2 | c2
                    · exact Or.inr (Or.inr (Or.inl ⟨c1, ⟨c2, c3⟩, c4⟩))
                    · subst c2
                      simp [Formula.opUnDi] at c4
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Eq.symm c4))))
                  · exact Or.inl c }
          use Sum.inr ()
          simp [f, r]
      case neg A_nd =>  -- just look up one and dont even recurse
        have ⟨y, y_pf⟩ := box_subproof 𝕏 x C Γ box_in rule
        use {
          X := 𝕏.X ⊕ Unit
          α
          | Sum.inl x => T.map (Sum.inl) (𝕏.α x)
          | Sum.inr z => ⟨RuleApp.box (Γ ∪ {A}) C (by simp_all), [Sum.inl y]⟩
          h := by
            intro x
            rcases x with x1 | x2
            · simp [r]
              have := 𝕏.h x1
              cases r_def : (𝕏.α x1).1 <;> simp_all [r, p]
              · convert this
            · simp_all only [r]
              simp only [T, p, List.map, y_pf, fₙ_alternate, List.cons.injEq, and_true]
              apply congr_arg₂
              · apply Finset.ext
                intro E
                simp only [D, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filterMap]
                constructor
                · aesop
                · intro mpp
                  rcases mpp with ⟨⟨c1, c2⟩, c3⟩ | ⟨c1, ⟨c2, c3⟩, c4⟩
                  · rcases c1 with c1 | c1
                    · exact Or.inl ⟨⟨c1, c2⟩, c3⟩
                    · exfalso; subst c1; exact A_nd c3
                  · rcases c2 with c2 | c2
                    · exact Or.inr ⟨c1, ⟨c2, c3⟩, c4⟩
                    · cases c1 <;> simp [Formula.opUnDi] at c4
                      · subst c4 c2
                        exfalso
                        simp [Formula.isDiamond] at A_nd
              · rfl }
        use Sum.inr ()
        simp [f, r]
termination_by (Formula.size A, Sequent.size_without_diamond Δ) -- Sequent.size_without_diamond
decreasing_by
  · simp [f, rule] at x_Δ
    subst x_Δ
    apply Prod.Lex.right _ for_term1
  · simp [f, rule] at x_Δ
    subst x_Δ
    apply Prod.Lex.right _ for_term2
  · apply Prod.Lex.right _
    subst x_Δ
    exact for_termination
  · rename_i eq
    subst eq
    apply Prod.Lex.left
    simp [Formula.size]

lemma helper {A B : Formula} : {A, ~A} ∪ {~B} = {A&B, ~A, ~B} \ {A&B} ∪ ({A} : Sequent) := by
  ext C
  simp
  apply Iff.intro
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only [or_true]
    | inr h_1 =>
      cases h_1 with
      | inl h =>
        subst h
        simp_all only [true_or, or_true, true_and]
        left
        have := Decidable.decide ((~A) = (A&B))
        sorry -- why doesnt this work??? ohhhhh because ~ is not apart of the language, no that shouldn't matter we still have decidableEq for formulas
      | inr h_2 =>
        subst h_2
        simp_all only [or_true, true_and]
        sorry
  · intro a
    cases a with
    | inl h =>
      obtain ⟨left, right⟩ := h
      simp_all only [false_or, or_true]
    | inr h_1 =>
      subst h_1
      simp_all only [true_or]

theorem extended_lem (A : Formula) : ∃ (𝕏 : Proof), 𝕏 ⊢ {A, ~A} := by
  induction A <;> simp only [Formula.neg]
  case bottom =>
    use {
      X := Unit
      α x := ⟨RuleApp.top {⊥,⊤} (by simp), {}⟩ -- : RuleApp × Finset Formula × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
    rfl
  case top =>
    use {
      X := Unit
      α x := ⟨RuleApp.top {⊤,⊥} (by simp), {}⟩ -- : RuleApp × Finset Formula × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
    rfl
  case atom n =>
    use {
      X := Unit
      α x := ⟨RuleApp.ax {at n, na n} n (by simp), {}⟩ -- : RuleApp × Finset Formula × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
  case neg_atom n =>
    use {
      X := Unit
      α x := ⟨RuleApp.ax {na n, at n} n (by simp), {}⟩ -- : RuleApp × Finset Formula × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
  case and A B ihA ihB =>
    have ⟨𝕏, x, x_A⟩ := weakening (~B) {A,~A} ihA
    have ⟨𝕐, y, y_B⟩ := weakening (~A) {B,~B} ihB
    let X := 𝕏.X ⊕ 𝕐.X ⊕ Bool -- prob need like 2 things here
    let α : X → T.obj X  -- : RuleApp × Finset Formula × Multiset X
      | Sum.inl x => T.map (Sum.inl) (𝕏.α x)
      | Sum.inr (Sum.inl x) => T.map (Sum.inr ∘ Sum.inl) (𝕐.α x)
      | Sum.inr (Sum.inr false) => ⟨RuleApp.or {A & B, (~A) v (~B)} (~A) (~B) (by simp), [Sum.inr $ Sum.inr true]⟩
      | Sum.inr (Sum.inr true) => ⟨RuleApp.and {A & B, (~A), (~B)} A B (by simp), [Sum.inl x, Sum.inr $ Sum.inl y]⟩
    use ⟨X, α, by
      intro x
      rcases x with x1 | x2 | x3
      · simp [r, α]
        have := 𝕏.h x1
        cases r_def : (𝕏.α x1).1 <;> simp_all [r, p]
        · convert this
      · simp [r, α]
        have := 𝕐.h x2
        cases r_def : (𝕐.α x2).1 <;> simp_all [r, p]
        · convert this
      · cases x3
        · simp only [α, r, p, fₙ_alternate, List.map_singleton, f, List.cons.injEq, and_true]
          aesop
        · simp_all only [r, α]
          simp only [T, p, List.map_cons, x_A, y_B,
            List.map_nil, List.cons.injEq, and_true]
          cases r_defl : (𝕏.α x).1 <;> cases r_defr : (𝕐.α y).1 <;> simp only [fₙ_alternate]
          all_goals
            sorry -- this is super easy we just want to solve it neatly
            ⟩
    use Sum.inr (Sum.inr false)
    simp [r, f, α]
  case or A B ihA ihB => -- see case above
    sorry
  case box A ihA =>
    have ⟨𝕏, x, x_A⟩ := weakening (◇A) {A,~A} ihA
    let X := 𝕏.X ⊕ Unit
    let α : X → T.obj X  -- : RuleApp × Finset Formula × Multiset X
      | Sum.inl x => T.map (Sum.inl) (𝕏.α x)
      | Sum.inr z => ⟨RuleApp.box {□A, ◇(~A)} A (by simp), [Sum.inl x]⟩
    use ⟨X, α, by
      intro x
      rcases x with x1 | x2
      · simp [r, α]
        have := 𝕏.h x1
        cases r_def : (𝕏.α x1).1 <;> simp_all [r, p]
        · convert this
      · simp_all only [r, α]
        simp only [T, p, List.map_cons, x_A,
          List.map_nil, List.cons.injEq, and_true]
        cases r_defl : (𝕏.α x).1 <;> simp only [fₙ_alternate]
        all_goals
          sorry -- want to solve this neatly
      ⟩
    use Sum.inr ()
    simp [r, f, α]
  all_goals
    sorry
