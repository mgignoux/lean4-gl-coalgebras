import GL.Logic
import Mathlib.Data.List.Chain

universe u

namespace Split
inductive RuleApp
  | topₗ : (Δ : SplitSequent) → (Sum.inl ⊤) ∈ Δ → RuleApp
  | topᵣ : (Δ : SplitSequent) → (Sum.inr ⊤) ∈ Δ → RuleApp
  | axₗₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp
  | axₗᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp
  | axᵣₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp
  | axᵣᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp
  | andₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A & B) ∈ Δ → RuleApp
  | andᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A & B) ∈ Δ → RuleApp
  | orₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A v B) ∈ Δ → RuleApp
  | orᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A v B) ∈ Δ → RuleApp
  | boxₗ : (Δ : SplitSequent) → (A : Formula) → Sum.inl (□ A) ∈ Δ → RuleApp
  | boxᵣ : (Δ : SplitSequent) → (A : Formula) → Sum.inr (□ A) ∈ Δ → RuleApp

def RuleApp.isBox : RuleApp → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

@[simp] def T : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨λ X ↦ ((RuleApp × List X) : Type u), by rintro X Y f ⟨r, A⟩; exact ⟨r, A.map f⟩, by aesop_cat, by aesop_cat⟩

def fₚ : RuleApp → SplitSequent
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

def f : RuleApp → SplitSequent
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

def fₙ : RuleApp → SplitSequent := fun Γ ↦ f Γ \ fₚ Γ

theorem fₙ_alternate (r : RuleApp) : fₙ r = match r with
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

theorem fₙ_sub_f {r : RuleApp} : fₙ r ⊆ f r := by simp [fₙ]

def r {X : Type u} (α : X → T.obj X) (x : X) := (α x).1
def p {X : Type u} (α : X → T.obj X) (x : X) := (α x).2
def edge {X : Type u} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

structure Proof where
  X : Type
  α : X → T.obj X
  h : ∀ (x : X), match r α x with
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

def Proves (𝕏 : Proof) (Δ : SplitSequent) : Prop := ∃ x : 𝕏.X, f (r 𝕏.α x) = Δ
def SplitSequent.isTrue (Δ : SplitSequent) : Prop := ∃ (𝕏 : Proof), Proves 𝕏 Δ

infixr:6 "⊢" => Proves
prefix:40 "⊢" => SplitSequent.isTrue

def equiv (B : Formula) (A : Formula) : Prop :=
  (∃ (𝕏 : Proof), 𝕏 ⊢ {Sum.inl (~A), Sum.inr B}) ∧ (∃ (𝕏 : Proof), 𝕏 ⊢ {Sum.inr A, Sum.inl (~B)})
infixr:7 "≅" => equiv

/- LEMMAS -/

theorem edge_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : (edge 𝕏.α) x y) : f (r 𝕏.α y) ⊆ SplitSequent.FL (f (r 𝕏.α x)) := by
  unfold edge at x_y
  have := 𝕏.h x
  cases rule : r 𝕏.α x <;> simp only [rule] at this
  · exfalso; simp_all
  · exfalso; simp_all
  · exfalso; simp_all
  · exfalso; simp_all
  · exfalso; simp_all
  · exfalso; simp_all
  case andₗ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_cons, List.not_mem_nil, or_false] at x_y
    rcases x_y with h|h <;> rw [h]
    · simp only [SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      intro χ χ_cases
      rcases χ_cases with h|_ <;> subst_eqs
      · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
      · exact ⟨Sum.inl (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · simp only [SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      intro χ χ_cases
      rcases χ_cases with h|_ <;> subst_eqs
      · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
      · exact ⟨Sum.inl (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case andᵣ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_cons, List.not_mem_nil, or_false] at x_y
    rcases x_y with h|h <;> rw [h]
    · simp only [SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      intro χ χ_cases
      rcases χ_cases with h|_ <;> subst_eqs
      · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
      · exact ⟨Sum.inr (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · simp only [SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      intro χ χ_cases
      rcases χ_cases with h|_ <;> subst_eqs
      · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
      · exact ⟨Sum.inr (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case orₗ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Finset.union_insert, SplitSequent.FL, Finset.subset_iff, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with _|h|_ <;> subst_eqs
    · exact ⟨Sum.inl (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inl (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case orᵣ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Finset.union_insert, SplitSequent.FL, Finset.subset_iff, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with _|h|_ <;> subst_eqs
    · exact ⟨Sum.inr (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inr (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case boxₗ Δ φ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with h|_ <;> subst_eqs
    · simp [SplitSequent.D] at h
      rcases h with ⟨h,_⟩|h
      · refine ⟨χ, fₙ_sub_f h, by simp [SplitFormula.FL_refl]⟩
      · rcases χ with χ | χ
        · refine ⟨Sum.inl (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simp at h; exact h)
        · refine ⟨Sum.inr (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simp at h; exact h)
    · exact ⟨Sum.inl (□φ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case boxᵣ Δ φ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with h|_ <;> subst_eqs
    · simp [SplitSequent.D] at h
      rcases h with ⟨h,_⟩|h
      · refine ⟨χ, fₙ_sub_f h, by simp [SplitFormula.FL_refl]⟩
      · rcases χ with χ | χ
        · refine ⟨Sum.inl (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simp at h; exact h)
        · refine ⟨Sum.inr (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simp at h; exact h)
    · exact ⟨Sum.inr (□φ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩

theorem path_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y) : f (r 𝕏.α y) ⊆ SplitSequent.FL (f (r 𝕏.α x)) := by
  induction x_y
  case refl => exact SplitSequent.FL_refl
  case tail y z x_y y_z fy_fx =>
    apply Finset.Subset.trans (edge_in_FL y_z)
    apply SplitSequent.FL_subset at fy_fx
    simp only [SplitSequent.FL_idem] at fy_fx
    exact fy_fx

/- POINT GENERATED PROOFS -/

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
    cases r_def : (𝕐.α y).1 <;> simp_all only [p, α_point, List.pmap, List.map_pmap, List.pmap_eq_map, List.empty_eq]

lemma node_in_pg_sequent_in_FL (𝕏 : Proof) (x : 𝕏.X) : ∀ y : (PointGeneratedProof 𝕏 x).X, f (r (α_point 𝕏 x) y) ⊆ SplitSequent.FL (f (r 𝕏.α x)) := by
  simp [PointGeneratedProof, r]
  intro y x_y
  exact path_in_FL x_y


/- FILTRATIONS -/

instance instSetoidXSplit (𝕏 : Proof) : Setoid 𝕏.X where
  r x y := f (r 𝕏.α x) = f (r 𝕏.α y)
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot 𝕐 (x : Quotient (instSetoidXSplit 𝕐)) :=
  T.map (Quotient.mk (instSetoidXSplit 𝕐)) (𝕐.α (Quotient.out x))


set_option maxHeartbeats 300000
noncomputable def Filtration (𝕐 : Proof) : Proof where
  X := Quotient (instSetoidXSplit 𝕐)
  α := α_quot 𝕐
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidXSplit 𝕐) x
      have h := 𝕐.h (@Quotient.out _ (instSetoidXSplit 𝕐) ⟦x⟧)
      simp only [r,p,α_quot,T] at *
      convert h <;> simp_all
      all_goals
        intro x x_in
        exact hyp x

/- GENERATED COALGEBRA -/


/- FINITENESS -/
theorem finite_proof_of_proof (𝕏 : Proof) (Δ : SplitSequent) : (𝕏 ⊢ Δ) → ∃ 𝕐, Finite 𝕐.X ∧ (𝕐 ⊢ Δ) := by
  intro X_proves_Δ
  have ⟨x, f_Δ⟩ := X_proves_Δ
  use PointGeneratedProof (Filtration 𝕏) (Quotient.mk (instSetoidXSplit 𝕏) x)
  constructor
  -- · refine ⟨?_, by simp⟩ -- just to get rid of the true thing
  · have h : Finite (SplitSequent.FL Δ).powerset := by
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
  · use ⟨Quotient.mk (instSetoidXSplit 𝕏) x, Relation.ReflTransGen.refl⟩
    rw [←f_Δ]
    simp [r, Filtration, PointGeneratedProof]
    exact Quotient.mk_out x

/- WIP : PARTIAL INTERPOLATION PROOFS -/

def nb_edge {X : Type u} (α : X → T.obj X) (x y : X) := y ∈ p α x ∧ ¬ (r α x).isBox

lemma lt_if_not_box_edge {𝕏 : Proof} {x y : 𝕏.X} : (x_y : nb_edge 𝕏.α x y) → (f (r 𝕏.α y)).size < (f (r 𝕏.α x)).size := by
  intro ⟨x_y, not_box⟩
  have h := 𝕏.h x
  cases r_def : (r 𝕏.α x) <;> simp_all only
  case andₗ Δ A B and_in =>
    have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) x_y
    simp [h, -Finset.union_singleton] at this
    rcases this with c | c
    all_goals
    · rw [c]
      simp [fₙ, f, fₚ, SplitSequent.size, -Finset.union_singleton]
      apply helper and_in (by simp [SplitFormula.size, Formula.size]; linarith)
  case andᵣ Δ A B and_in =>
    have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) x_y
    simp [h, -Finset.union_singleton] at this
    rcases this with c | c
    all_goals
    · rw [c]
      simp [fₙ, f, fₚ, SplitSequent.size, -Finset.union_singleton]
      apply helper and_in (by simp [SplitFormula.size, Formula.size]; linarith)
  case orₗ Δ A B or_in =>
    have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) x_y
    simp only [h, List.mem_singleton] at this
    rw [this]
    simp only [fₙ, f, fₚ, SplitSequent.size]
    apply helper or_in (by
      by_cases A = B
      · subst_eqs
        simp [SplitFormula.size, Formula.size]
        linarith
      · have := @Finset.sum_union _ _ {Sum.inl A} {Sum.inl B} _ SplitFormula.size _ (by aesop)
        simp_all [SplitFormula.size, Formula.size])
  case orᵣ Δ A B or_in =>
    have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) x_y
    simp only [h, List.mem_singleton] at this
    rw [this]
    simp only [fₙ, f, fₚ, SplitSequent.size]
    apply helper or_in (by
      by_cases A = B
      · subst_eqs
        simp [SplitFormula.size, Formula.size]
        linarith
      · have := @Finset.sum_union _ _ {Sum.inr A} {Sum.inr B} _ SplitFormula.size _ (by aesop)
        simp_all [SplitFormula.size, Formula.size])
  all_goals
    simp_all [RuleApp.isBox]

lemma lt_if_not_box_path {𝕏 : Proof} {x y : 𝕏.X} : Relation.TransGen (nb_edge 𝕏.α) x y →
      (f (r 𝕏.α y)).size < (f (r 𝕏.α x)).size := by
  intro x_y
  induction x_y
  case single x_y => exact lt_if_not_box_edge x_y
  case tail y z x_y y_z ih => exact Nat.lt_trans (lt_if_not_box_edge y_z) ih

theorem no_non_box_loop {𝕏 : Proof} (x : 𝕏.X) : ¬ (Relation.TransGen (nb_edge 𝕏.α) x x) := by
  intro con
  apply lt_if_not_box_path at con
  simp at con

theorem exists_box_on_le_path {𝕏 : Proof} (x y : 𝕏.X) : Relation.TransGen (edge 𝕏.α) x y → (f (r 𝕏.α x)).size ≤ (f (r 𝕏.α y)).size
  → ∃ z, Relation.ReflTransGen (edge 𝕏.α) x z ∧ Relation.ReflTransGen (edge 𝕏.α) z y ∧ (r 𝕏.α z).isBox := by
  intro x_y size_le
  induction x_y
  case single y x_y =>
    by_cases (r 𝕏.α x).isBox
    case pos h => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.single x_y, h⟩
    case neg h =>
      have := lt_if_not_box_edge ⟨x_y, h⟩
      linarith
  case tail y z x_y y_z ih =>
    by_cases (r 𝕏.α y).isBox
    case pos h => exact ⟨y, x_y.to_reflTransGen, Relation.ReflTransGen.single y_z, h⟩
    case neg h =>
      have ⟨u, x_u, u_y, u_box⟩ := ih (LE.le.trans size_le (Nat.le_of_lt (lt_if_not_box_edge ⟨y_z, h⟩)))
      exact ⟨u, x_u, u_y.tail y_z, u_box⟩

lemma exists_box_on_loop {𝕏 : Proof} (x : 𝕏.X) : Relation.TransGen (edge 𝕏.α) x x
    → ∃ z, Relation.ReflTransGen (edge 𝕏.α) x z ∧ Relation.ReflTransGen (edge 𝕏.α) z x ∧ (r 𝕏.α z).isBox :=
  fun x_x ↦ exists_box_on_le_path x x x_x (by simp)


def edge_restr {𝕏 : Proof} (p : 𝕏.X → Prop) : 𝕏.X → 𝕏.X → Prop := fun x y ↦ edge 𝕏.α x y ∧ p x ∧ p y

lemma exists_box_on_le_restr_path {𝕏 : Proof} (x y : 𝕏.X) (p : 𝕏.X → Prop) :
  Relation.TransGen (edge_restr p) x y → (f (r 𝕏.α x)).size ≤ (f (r 𝕏.α y)).size
    → ∃ z, Relation.ReflTransGen (edge_restr p) x z ∧ Relation.TransGen (edge_restr p) z y ∧ (r 𝕏.α z).isBox := by
  intro x_y size_le
  induction x_y
  case single y x_y =>
    by_cases (r 𝕏.α x).isBox
    case pos h => exact ⟨x, Relation.ReflTransGen.refl, Relation.TransGen.single x_y, h⟩
    case neg h =>
      have := lt_if_not_box_edge ⟨x_y.1, h⟩
      linarith
  case tail y z x_y y_z ih =>
    by_cases (r 𝕏.α y).isBox
    case pos h => exact ⟨y, x_y.to_reflTransGen, Relation.TransGen.single y_z, h⟩
    case neg h =>
      have ⟨u, x_u, u_y, u_box⟩ := ih (LE.le.trans size_le (Nat.le_of_lt (lt_if_not_box_edge ⟨y_z.1, h⟩)))
      exact ⟨u, x_u, u_y.tail y_z, u_box⟩

lemma exists_box_on_restr_loop {𝕏 : Proof} (x : 𝕏.X) (p : 𝕏.X → Prop) : Relation.TransGen (edge_restr p) x x
    → ∃ z, (r 𝕏.α z).isBox ∧ p z ∧ Relation.TransGen (edge_restr p) z z := by
  intro x_x
  have ⟨z, z_prop⟩ := exists_box_on_le_restr_path x x p x_x (by simp)
  refine ⟨z, z_prop.2.2, ?_, Relation.TransGen.trans z_prop.2.1 ?_⟩
  · cases z_prop.1
    case refl =>
      cases x_x
      case single x_x => exact x_x.2.2
      case tail _x => exact _x.2.2
    case tail _z => exact _z.2.2
  · cases z_prop.1
    case refl => exact x_x
    case tail x_ _z => apply Relation.TransGen.trans_right x_ (Relation.TransGen.single _z)


theorem inf_path_has_inf_boxes {𝕏 : Proof} (g : ℕ → 𝕏.X) (h : ∀ n, edge 𝕏.α (g n) (g (n + 1))) :
  ∀ n, ∃ m, (r 𝕏.α (g (n + m))).isBox := by
    intro n
    by_contra h2
    simp at h2
    apply (wellFounded_iff_isEmpty_descending_chain.1 (@wellFounded_lt ℕ _ _)).false
    use fun m ↦ SplitSequent.size (f (r 𝕏.α (g (n + m))))
    intro m
    apply lt_if_not_box_edge ⟨h (n + m), h2 m⟩

--  Relation.TransGen (fun y1 y2 ↦ edge 𝕏.α y1 y2 ∧ (y1 ∈ Y ∧ y2 ∈ Y)) y y
-- wellfounded)iff)isEnoty
