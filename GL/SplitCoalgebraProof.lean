import GL.CoalgebraProof
import Mathlib.Data.List.Chain

namespace split

universe u

abbrev SplitFormula := Formula ⊕ Formula
abbrev SplitSequent := Finset SplitFormula
namespace SplitFormula

def isDiamond : Formula ⊕ Formula -> Prop
  | Sum.inl (◇_) => true
  | Sum.inr (◇_) => true
  | _ => false

def opUnDi (A : Formula ⊕ Formula) : Option (Formula ⊕ Formula) := match A with
  | Sum.inl (◇B) => Option.some (Sum.inl B)
  | Sum.inr (◇B) => Option.some (Sum.inr B)
  | _ => none

instance : DecidablePred isDiamond := by
  intro A
  rcases A with A | A
  all_goals
  cases A <;> simp [isDiamond]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp

def size : (Formula ⊕ Formula) → Nat
  | Sum.inl A => A.size
  | Sum.inr A => A.size

end SplitFormula

def D (Γ : SplitSequent) : SplitSequent
  := Finset.filter SplitFormula.isDiamond Γ ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  rcases A with A | A <;> rcases B with B | B <;> rcases C with C | C
  all_goals
  simp_all
  cases A <;> cases B
  all_goals
    simp_all [SplitFormula.opUnDi])

namespace SplitSequent

def toSequent (Δ : SplitSequent) : Sequent := Finset.image (Sum.elim id id) Δ
def size (Δ : SplitSequent) : Nat := Finset.sum Δ (SplitFormula.size)

end SplitSequent

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

def r {X : Type u} (α : X → T.obj X) (x : X) := (α x).1
def p {X : Type u} (α : X → T.obj X) (x : X) := (α x).2
def edge {X : Type u} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

structure Proof where
  X : Type u
  decidable : DecidableEq X
  α : X → T.obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.andₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [D (fₙ (r α x)) ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [D (fₙ (r α x)) ∪ {Sum.inr A}]
    | _ => p α x = {}

instance instSetoidXSplit (𝕏 : Proof) : Setoid 𝕏.X where
  r x y := f (r 𝕏.α x) = f (r 𝕏.α y)
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot 𝕐 (x : Quotient (instSetoidXSplit 𝕐)) :=
  T.map (Quotient.mk (instSetoidXSplit 𝕐)) (𝕐.α (Quotient.out x))

/- FILTRATIONS -/

noncomputable def Filtration (𝕐 : Proof) : Proof where
  X := Quotient (instSetoidXSplit 𝕐)
  decidable := @Quotient.decidableEq _ _ (by
    intro a b
    simp [HasEquiv.Equiv, instSetoidXSplit]
    apply Finset.decidableEq)
  α := α_quot 𝕐
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
    --  have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidXSplit 𝕐) x
    --  have claim : f (fun x ↦ (T.map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidXSplit 𝕐)))) (𝕐.α (Quotient.out x))) ∘ (fun x ↦ ⟦x⟧) = fun x ↦ f (r 𝕐.α x) := by
    --   funext x
    --    rw [←(hyp x)]
    --    simp [f, fₚ, fₙ]
    -- sorry -- rewrite
    --  have h := 𝕐.h (@Quotient.out _ (instSetoidXSplit 𝕐) ⟦x⟧)
      sorry -- rewrite
      -- rcases h with ⟨bot1, bot2⟩ | ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩ | ⟨A, box1, box2⟩
      -- · refine Or.inl ⟨bot1, ?_⟩
      --   simp [p]
      --   exact bot2
      -- · refine Or.inr $ Or.inl ⟨bot1, ?_⟩
      --   simp [p]
      --   exact bot2
      -- · refine Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, and1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at and2
      --   rw [←and2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, and1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at and2
      --   rw [←and2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, or1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at or2
      --   rw [←or2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, or1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at or2
      --   rw [←or2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, box1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at box2
      --   rw [←box2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr ⟨A, box1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at box2
      --   rw [←box2]
      --   apply congr_arg₂ Multiset.map claim rfl


/- GENERATED COALGEBRA -/


/- FINITENESS -/


/- WIP : PARTIAL INTERPOLATION PROOFS -/

lemma helper {α : Type} [DecidableEq α] {A C : Finset α} {b : α} {f : α → Nat}
  : b ∈ A → C.sum f < f b → Finset.sum ((A \ {b}) ∪ C) f < Finset.sum A f := by
  intro b_in_A C_lt_B
  calc
    _ ≤ Finset.sum (A \ {b}) f + Finset.sum C f := by sorry -- another lemma for this?
    _ = Finset.sum A f - Finset.sum {b} f + Finset.sum C f := by
      simp [Sequent.jfef $ @Finset.sum_sdiff α Nat {b} A _ f _ (Finset.singleton_subset_iff.2 b_in_A)]

    _ < Finset.sum A f := by
      apply hm
      · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 b_in_A) (by simp))
      · exact C_lt_B


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
        sorry -- broken after update

        -- rw [this]
        -- simp [SplitFormula.size, Formula.size]
      )
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
        sorry -- broken after update

        -- rw [this]
        -- simp [SplitFormula.size, Formula.size]
      )
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
    → ∃ z, Relation.ReflTransGen (edge_restr p) x z ∧ Relation.ReflTransGen (edge_restr p) z y ∧ (r 𝕏.α z).isBox := by
  intro x_y size_le
  induction x_y
  case single y x_y =>
    by_cases (r 𝕏.α x).isBox
    case pos h => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.single x_y, h⟩
    case neg h =>
      have := lt_if_not_box_edge ⟨x_y.1, h⟩
      linarith
  case tail y z x_y y_z ih =>
    by_cases (r 𝕏.α y).isBox
    case pos h => exact ⟨y, x_y.to_reflTransGen, Relation.ReflTransGen.single y_z, h⟩
    case neg h =>
      have ⟨u, x_u, u_y, u_box⟩ := ih (LE.le.trans size_le (Nat.le_of_lt (lt_if_not_box_edge ⟨y_z.1, h⟩)))
      exact ⟨u, x_u, u_y.tail y_z, u_box⟩

lemma exists_box_on_restr_loop {𝕏 : Proof} (x : 𝕏.X) (p : 𝕏.X → Prop) : Relation.TransGen (edge_restr p) x x
    → ∃ z, (r 𝕏.α z).isBox ∧ p z := by -- this is a heavy simplification
  intro x_x
  have ⟨z, z_prop⟩ := exists_box_on_le_restr_path x x p x_x (by simp)
  refine ⟨z, z_prop.2.2, ?_⟩
  cases z_prop.1
  case refl =>
    cases x_x
    case single x_x => exact x_x.2.2
    case tail _x => exact _x.2.2
  case tail _z => exact _z.2.2


--  Relation.TransGen (fun y1 y2 ↦ edge 𝕏.α y1 y2 ∧ (y1 ∈ Y ∧ y2 ∈ Y)) y y
-- wellfounded)iff)isEnoty
