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

inductive Formula : Type
  | bottom : Formula
  | top : Formula
  | atom : Nat → Formula
  | neg_atom : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | box : Formula → Formula
  | diamond : Formula → Formula
deriving Repr,DecidableEq

abbrev Sequent := Finset Formula

namespace Formula

prefix:70 "at" => atom
prefix:70 "na" => neg_atom
prefix:70 "□" => box
prefix:70 "◇" => diamond
infixr:6 "&" => and
infixr:6 "v" => or

instance : Bot (Formula) where bot := Formula.bottom
instance : Top (Formula) where top := Formula.top

def isAtomic : Formula -> Prop
  | at _ => true
  | _ => false

def isNegAtomic : Formula -> Prop
  | na _ => true
  | _ => false

def isDiamond : Formula -> Prop
  | ◇_ => true
  | _ => false

def opUnDi (A : Formula) : Option Formula := match A with
  | ◇ B => Option.some B
  | _ => none

@[simp]
theorem opUnDi_eq {φ ψ : Formula} : φ.opUnDi = some ψ ↔ φ = ◇ ψ := by
  cases φ <;> simp [Formula.opUnDi]

def unDi (A : Formula) (h : A.isDiamond) : Formula := match A with
  | ◇ B => B

def isBox : Formula -> Prop
  | □_ => true
  | _ => false

instance : DecidablePred Formula.isAtomic := by
  intro A
  cases A <;> simp [isAtomic]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp

instance : DecidablePred isNegAtomic := by
  intro A
  cases A <;> simp [isNegAtomic]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp

instance : DecidablePred isDiamond := by
  intro A
  cases A <;> simp [isDiamond]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp

instance : DecidablePred isBox := by
  intro A
  cases A <;> simp [isBox]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp

@[simp] def neg : Formula → Formula
  | ⊥ => ⊤
  | ⊤ => ⊥
  | at n => na n
  | na n => at n
  | A & B => (neg A) v (neg B)
  | A v B => (neg A) & (neg B)
  | □ A => ◇ (neg A)
  | ◇ A => □ (neg A)

prefix:50 "~" => Formula.neg
notation:55 φ:56 " ↣ " ψ:55 => (~ φ) v ψ
notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) & (ψ ↣ φ)
prefix:50 " ⊡ " => fun φ ↦ φ & (□ φ)


@[simp]
theorem neg_neg_eq (φ : Formula) : (~~φ) = φ := by induction φ <;> simp [Formula.instBot, Formula.instTop] <;> grind

def P := at 0
def Q := at 1

def size : Formula → Nat
  | ⊥ => 0
  | ⊤ => 0
  | at _ => 1
  | na _ => 1
  | A & B => size A + size B + 1
  | A v B => size A + size B + 1
  | □ A => size A + 1
  | ◇ A => size A + 1

def pp_form : Formula → String
  | ⊥ => "⊥"
  | ⊤ => "⊤"
  | at n => "P" ++ Nat.toSubscriptString n
  | na n => "¬P" ++ Nat.toSubscriptString n
  | A & B => "(" ++ pp_form A ++ "∧" ++ pp_form B ++ ")"
  | A v B => "(" ++ pp_form A ++ "∨" ++ pp_form B ++ ")"
  | □ A => "□" ++ pp_form A
  | ◇ A => "◇" ++ pp_form A

def vocab : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na n => {n}
  | A & B => vocab A ∪ vocab B
  | A v B => vocab A ∪ vocab B
  | □ A => vocab A
  | ◇ A => vocab A

def atoms : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na _ => ∅
  | A & B => vocab A ∪ vocab B
  | A v B => vocab A ∪ vocab B
  | □ A => vocab A
  | ◇ A => vocab A

  /-- Get a fresh atomic proposition `x` not occuring in `A`. -/
def freshVar : Formula → Nat
  | ⊤  => 0
  | ⊥  => 0
  | at n  => n + 1
  | na n  => n + 1
  | A & B  => max (freshVar A) (freshVar B)
  | A v B  =>  max (freshVar A) (freshVar B)
  | □ A  => freshVar A
  | ◇ A  => freshVar A

def FL : Formula → Sequent
  | ⊥ => {⊥}
  | ⊤ => {⊤}
  | at n => {at n}
  | na n => {na n}
  | φ v ψ => {φ v ψ} ∪ FL φ ∪ FL ψ
  | φ & ψ => {φ & ψ} ∪ FL φ ∪ FL ψ
  | □ φ => {□ φ} ∪ FL φ
  | ◇ φ => {◇ φ} ∪ FL φ

/- Lemmas about FL closure -/

theorem FL_refl {φ : Formula} : φ ∈ FL φ := by cases φ <;> simp [FL, instBot, instTop]

theorem FL_mon {φ ψ : Formula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
  cases φ <;> simp_all [FL]
  · rcases ψ_sub_φ with _|ψ_sub|ψ_sub <;> subst_eqs
    · simp [FL]
    · have := FL_mon ψ_sub
      intro x x_in
      simp; right; left; exact this x_in
    · have := FL_mon ψ_sub
      intro x x_in
      simp; right; right; exact this x_in
  · rcases ψ_sub_φ with _|ψ_sub|ψ_sub <;> subst_eqs
    · simp [FL]
    · have := FL_mon ψ_sub
      intro x x_in
      simp; right; left; exact this x_in
    · have := FL_mon ψ_sub
      intro x x_in
      simp; right; right; exact this x_in
  · rcases ψ_sub_φ with _|ψ_sub <;> subst_eqs
    · simp [FL]
    · have := FL_mon ψ_sub
      intro x x_in
      simp; right; exact this x_in
  · rcases ψ_sub_φ with _|ψ_sub <;> subst_eqs
    · simp [FL]
    · have := FL_mon ψ_sub
      intro x x_in
      simp; right; exact this x_in


end Formula

namespace Sequent

def size (Γ : Sequent) : Nat := Finset.sum Γ Formula.size

unsafe def pp_form (Γ : Sequent) : String := String.intercalate "," ((Quot.unquot Γ.val).map Formula.pp_form)

def FL : Sequent → Sequent := fun Δ ↦ Finset.biUnion Δ Formula.FL

/- Lemmas about FL Closure of Sequents -/

theorem FL_refl {Δ : Sequent} : Δ ⊆ FL Δ := by
  simp [Finset.subset_iff, FL]
  intro x x_in
  exact ⟨x, x_in, Formula.FL_refl⟩

theorem FL_subset {Δ Γ : Sequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  simp_all [Finset.subset_iff, FL]
  intro φ ψ ψ_in_Δ φ_sub_ψ
  exact ⟨ψ, Δ_sub_Γ ψ_in_Δ, φ_sub_ψ⟩

theorem FL_idem {Δ : Sequent} : FL (FL Δ) = FL Δ := by
  simp [Finset.Subset.antisymm_iff]
  constructor
  · simp [Finset.subset_iff, FL]
    intro φ ψ χ χ_in_Δ φ_sub_χ φ_sub_ψ
    exact ⟨χ, χ_in_Δ, by apply Formula.FL_mon φ_sub_χ; simp_all⟩
  · exact FL_subset (FL_refl)


/- Helper Lemmas about Finset -/

def size_without_diamond (Γ : Sequent) : Nat := Finset.sum (Γ.filter (λ A ↦ ¬ (Formula.isDiamond A))) Formula.size

/-- Delete me! -/
lemma jfef {n m l : Nat} : n + m = l → n = l - m := by
intro a
subst a
simp_all only [add_tsub_cancel_right]

/-- I should be in Mathlib! -/
lemma Finset.filter_sdiff {Γ Δ : Sequent} : (Γ \ Δ).filter (λ A ↦ ¬ (Formula.isDiamond A)) = Γ.filter (λ A ↦ ¬ (Formula.isDiamond A)) \ Δ.filter (λ A ↦ ¬ (Formula.isDiamond A)) := by
  apply Finset.ext
  intro A
  simp
  constructor
  · intro ⟨⟨A_in_Γ, A_ni_Δ⟩, A_di⟩
    exact ⟨⟨A_in_Γ, A_di⟩, fun x ↦ by exfalso; exact A_ni_Δ x⟩
  · intro ⟨⟨A_in_Γ, A_di⟩, mp⟩
    refine ⟨⟨A_in_Γ, fun x ↦ by exfalso; exact A_di (mp x)⟩, A_di⟩

theorem size_wod_sdiff {Γ Δ : Sequent} (h : Δ ⊆ Γ) : size_without_diamond (Γ \ Δ) = size_without_diamond Γ - size_without_diamond Δ := by
  have this := @Finset.sum_sdiff _ _ _ _ _ Formula.size _ (Finset.filter_subset_filter (λ A ↦ ¬ (Formula.isDiamond A)) h)
  have := jfef this
  simp only [size_without_diamond]
  rw [←this]
  have := @ Finset.filter_sdiff Γ Δ
  simp [this]

theorem size_wod_disjoint {Γ Δ : Sequent} :
  Disjoint Γ Δ → size_without_diamond (Γ ∪ Δ)
        = size_without_diamond Γ + size_without_diamond Δ := by
  intro dis
  have dis_diamond : Disjoint (Γ.filter (λ A ↦ ¬ (Formula.isDiamond A))) (Δ.filter (λ A ↦ ¬ (Formula.isDiamond A))):= by
    simp_all [Disjoint]
    intro Τ Τ_Γ' Τ_Δ'
    exact @dis Τ (Finset.Subset.trans Τ_Γ' (Finset.filter_subset _ _)) (Finset.Subset.trans Τ_Δ' (Finset.filter_subset _ _))
  simp only [size_without_diamond, Finset.filter_union (λ A ↦ ¬ (Formula.isDiamond A)) Γ Δ]
  exact Finset.sum_union dis_diamond

def vocab (Γ : Sequent) : Finset Nat := Finset.biUnion Γ Formula.vocab

def freshVar (Γ : Finset Formula) : Nat :=
  if h : Γ = {} then 0 else Finset.max' (Γ.image (Formula.freshVar)) (by
    by_contra con
    simp_all)

end Sequent

abbrev SplitFormula := Formula ⊕ Formula
abbrev SplitSequent := Finset SplitFormula

namespace SplitFormula
def isDiamond : SplitFormula -> Prop
  | Sum.inl (◇_) => true
  | Sum.inr (◇_) => true
  | _ => false

def opUnDi (A : SplitFormula) : Option SplitFormula := match A with
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

def FL : SplitFormula → SplitSequent
  | Sum.inl ⊥ => {Sum.inl ⊥}
  | Sum.inr ⊥ => {Sum.inr ⊥}
  | Sum.inl ⊤ => {Sum.inl ⊤}
  | Sum.inr ⊤ => {Sum.inr ⊤}
  | Sum.inl (at n) => {Sum.inl (at n)}
  | Sum.inr (at n) => {Sum.inr (at n)}
  | Sum.inl (na n) => {Sum.inl (na n)}
  | Sum.inr (na n) => {Sum.inr (na n)}
  | Sum.inl (φ v ψ) => {Sum.inl (φ v ψ)} ∪ FL (Sum.inl φ) ∪ FL (Sum.inl ψ)
  | Sum.inr (φ v ψ) => {Sum.inr (φ v ψ)} ∪ FL (Sum.inr φ) ∪ FL (Sum.inr ψ)
  | Sum.inl (φ & ψ) => {Sum.inl (φ & ψ)} ∪ FL (Sum.inl φ) ∪ FL (Sum.inl ψ)
  | Sum.inr (φ & ψ) => {Sum.inr (φ & ψ)} ∪ FL (Sum.inr φ) ∪ FL (Sum.inr ψ)
  | Sum.inl (□ φ) => {Sum.inl (□ φ)} ∪ FL (Sum.inl φ)
  | Sum.inr (□ φ) => {Sum.inr (□ φ)} ∪ FL (Sum.inr φ)
  | Sum.inl (◇ φ) => {Sum.inl (◇ φ)} ∪ FL (Sum.inl φ)
  | Sum.inr (◇ φ) => {Sum.inr (◇ φ)} ∪ FL (Sum.inr φ)

theorem FL_SplitFormula_left_eq_FL_Formula_map (φ : Formula) : FL (Sum.inl φ) = φ.FL.map ⟨Sum.inl, by intro x; grind⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]

theorem FL_SplitFormula_right_eq_FL_Formula_map (φ : Formula) : FL (Sum.inr φ) = φ.FL.map ⟨Sum.inr, by intro x; grind⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]

theorem in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.isLeft := by
  induction φ <;> simp_all [FL] <;> grind

theorem in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.isRight := by
  induction φ <;> simp_all [FL] <;> grind

theorem in_FL_of_in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind

theorem in_FL_of_in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind

/- Lemmas about FL closure -/

theorem FL_refl {φ : SplitFormula} : φ ∈ FL φ := by rcases φ with φ | φ <;> cases φ <;> simp [FL, Formula.instBot, Formula.instTop]

theorem FL_mon {φ ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
  rcases φ with φ | φ
  · simp [FL_SplitFormula_left_eq_FL_Formula_map φ]
    have is_left := in_FL_SplitFormula_left ψ_sub_φ
    rcases ψ with ψ | ψ <;> simp_all
    simp [FL_SplitFormula_left_eq_FL_Formula_map ψ]
    apply Formula.FL_mon
    exact in_FL_of_in_FL_SplitFormula_left ψ_sub_φ
  · simp [FL_SplitFormula_right_eq_FL_Formula_map φ]
    have is_left := in_FL_SplitFormula_right ψ_sub_φ
    rcases ψ with ψ | ψ <;> simp_all
    simp [FL_SplitFormula_right_eq_FL_Formula_map ψ]
    apply Formula.FL_mon
    exact in_FL_of_in_FL_SplitFormula_right ψ_sub_φ

end SplitFormula

namespace SplitSequent

def FL : SplitSequent → SplitSequent := fun Δ ↦ Finset.biUnion Δ SplitFormula.FL

/- Lemmas about FL Closure of Sequents -/

theorem FL_refl {Δ : SplitSequent} : Δ ⊆ FL Δ := by
  simp [Finset.subset_iff, FL]
  constructor
  · intro x x_in
    left
    exact ⟨x, x_in, SplitFormula.FL_refl⟩
  · intro x x_in
    right
    exact ⟨x, x_in, SplitFormula.FL_refl⟩

theorem FL_subset {Δ Γ : SplitSequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  simp_all [Finset.subset_iff, FL]
  constructor
  all_goals
    intro φ h
    rcases h with h | h
    · have ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩ := h
      left
      refine ⟨ψ, Δ_sub_Γ.1 _ ψ_in_Δ, φ_sub_ψ⟩
    · have ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩ := h
      right
      refine ⟨ψ, Δ_sub_Γ.2 _ ψ_in_Δ, φ_sub_ψ⟩


theorem FL_idem {Δ : SplitSequent} : FL (FL Δ) = FL Δ := by
  simp [Finset.Subset.antisymm_iff]
  constructor
  · simp [Finset.subset_iff, FL]
    constructor
    all_goals
    intro φ h
    · rcases h with ⟨ψ, ⟨χ, χ_in_Δ, ψ_sub_χ⟩ | ⟨χ, χ_in_Δ, ψ_sub_χ⟩, φ_sub_ψ⟩ | ⟨ψ, ⟨χ, χ_in_Δ, ψ_sub_χ⟩ | ⟨χ, χ_in_Δ, ψ_sub_χ⟩, φ_sub_ψ⟩
      · left
        exact ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
      · right
        exact ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
      · left
        exact ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
      · right
        exact ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
  · exact FL_subset (FL_refl)

def D (Γ : SplitSequent) : SplitSequent
  := Finset.filter SplitFormula.isDiamond Γ ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  rcases A with A | A <;> rcases B with B | B <;> rcases C with C | C
  all_goals
  simp_all
  cases A <;> cases B
  all_goals
    simp_all [SplitFormula.opUnDi])

@[simp]
theorem opUnDi_eqₗₗ {φ ψ : Formula} : SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inl ψ) ↔ φ = ◇ ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
theorem opUnDi_eqᵣᵣ {φ ψ : Formula} : SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inr ψ) ↔ φ = ◇ ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
theorem opUnDi_eqₗᵣ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inr ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
theorem opUnDi_eqᵣₗ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inl ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]

def toSequent (Δ : SplitSequent) : Sequent := Finset.image (Sum.elim id id) Δ
def size (Δ : SplitSequent) : Nat := Finset.sum Δ (SplitFormula.size)

end SplitSequent




/- needs a new home -/
lemma hm {a b c : ℕ} : b ≤ a → (c < b) → (a - b) + c < a := by grind only [cases Or]

lemma helper {α : Type} [DecidableEq α] {A C : Finset α} {b : α} {f : α → Nat}
  : b ∈ A → C.sum f < f b → Finset.sum ((A \ {b}) ∪ C) f < Finset.sum A f := by
  intro b_in_A C_lt_B
  calc
    _ ≤ Finset.sum (A \ {b}) f + Finset.sum C f := by
     simp [Sequent.jfef $ @Finset.sum_union_inter _ _ (A \ {b}) C _ f _]
    _ = Finset.sum A f - Finset.sum {b} f + Finset.sum C f := by
      simp [Sequent.jfef $ @Finset.sum_sdiff α Nat {b} A _ f _ (Finset.singleton_subset_iff.2 b_in_A)]
    _ < Finset.sum A f := by
      apply hm
      · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 b_in_A) (by simp))
      · exact C_lt_B

instance {α} [DecidableEq α] (Γ : Finset α) : Union {x // x ∈ Γ.powerset} where -- mathlib ????
  union A B := ⟨A ∪ B, by
    apply Finset.mem_powerset.2
    apply Finset.subset_iff.2
    intro x h
    rcases (Finset.mem_union.1 h) with h | h
    · apply Finset.mem_of_subset (Finset.mem_powerset.1 A.2) h
    · apply Finset.mem_of_subset (Finset.mem_powerset.1 B.2) h
    ⟩
