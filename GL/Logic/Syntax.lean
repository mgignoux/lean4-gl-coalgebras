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

/-! ## Syntax of Basic Modal Logic

Here we supply basic definitions, abbreviations, and lemmas about the syntax of BML.
-/

/-- Type of BML Formulas. -/
inductive Formula : Type
  | bottom : Formula
  | top : Formula
  | atom : Nat → Formula
  | negAtom : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | box : Formula → Formula
  | diamond : Formula → Formula
deriving Repr,DecidableEq

/-- A sequent is a finite set of formulas, read disjunctively. -/
abbrev Sequent := Finset Formula

namespace Formula

prefix:70 "at" => atom
prefix:70 "na" => negAtom
prefix:70 "□" => box
prefix:70 "◇" => diamond
infixr:6 "&" => and
infixr:6 "v" => or

@[simp] instance instBot : Bot (Formula) where bot := Formula.bottom
@[simp] instance instTop : Top (Formula) where top := Formula.top

/-- Negation of a BML Formula. -/
@[simp] def neg : Formula → Formula
  | ⊥ => ⊤
  | ⊤ => ⊥
  | at n => na n
  | na n => at n
  | φ & ψ => (neg φ) v (neg ψ)
  | φ v ψ => (neg φ) & (neg ψ)
  | □ φ => ◇ (neg φ)
  | ◇ φ => □ (neg φ)

prefix:50 "~" => Formula.neg
notation:55 φ:56 " ↣ " ψ:55 => (~ φ) v ψ
notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) & (ψ ↣ φ)
prefix:50 " ⊡ " => fun φ ↦ φ & (□ φ)

/-! # Basic operations and simp lemmas for Formulas -/

/-- Returns `true` if the formula is a propositional atom `at n`. -/
def isAtomic : Formula → Bool
  | at _ => true
  | _ => false

/-- Returns `true` if the formula is a negated atom `na n`. -/
def isNegAtomic : Formula → Bool
  | na _ => true
  | _ => false

/-- Returns `true` if the formula is a diamond formula `◇ φ`. -/
def isDiamond : Formula → Bool
  | ◇ _ => true
  | _ => false

/-- Returns `some φ` if the formula is `◇ φ`, otherwise `none`. -/
def opUnDi (φ : Formula) : Option Formula := match φ with
  | ◇ φ => Option.some φ
  | _ => none

@[simp] lemma opUnDi_eq {φ ψ : Formula} : φ.opUnDi = some ψ ↔ φ = ◇ ψ := by
  cases φ <;> simp [Formula.opUnDi]

/-- Extracts `φ` from `◇ φ`, given a proof that the formula is a diamond. -/
def unDi (φ : Formula) (h : φ.isDiamond) : Formula := match φ with
  | ◇ φ => φ

/-- Returns `true` if the formula is a box formula `□ φ`. -/
def isBox : Formula → Bool
  | □ _ => true
  | _ => false


/-- Negation is injective. -/
@[simp] lemma neg_eq {φ ψ : Formula} : (~φ) = (~ψ) → φ = ψ := by
  intro mpp
  cases φ <;> cases ψ <;> simp [Formula.neg] at mpp <;> try grind
  case and.and φ₁ φ₂ φ₃ φ₄ =>
    have := neg_eq mpp.1
    have := neg_eq mpp.2
    grind
  case or.or φ₁ φ₂ φ₃ φ₄ =>
    have := neg_eq mpp.1
    have := neg_eq mpp.2
    grind
  case box.box φ₁ φ₂ =>
    have := neg_eq mpp
    grind
  case diamond.diamond φ₁ φ₂ =>
    have := neg_eq mpp
    grind

/-- Negation is involutive. -/
@[simp]
lemma neg_neg_eq (φ : Formula) : (~~φ) = φ := by induction φ <;> simp_all

/-- Length of a BML Formula. -/
def length : Formula → Nat
  | ⊥ => 0
  | ⊤ => 0
  | at _ => 1
  | na _ => 1
  | φ & ψ => length φ + length ψ + 1
  | φ v ψ => length φ + length ψ + 1
  | □ φ => length φ + 1
  | ◇ φ => length φ + 1


/-- Vocab of a BML Formula. Expressed as underlying natural numbers. -/
def vocab : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na n => {n}
  | φ & ψ => vocab φ ∪ vocab ψ
  | φ v ψ => vocab φ ∪ vocab ψ
  | □ φ => vocab φ
  | ◇ φ => vocab φ

/-- Atoms of a BML Formula. Expressed as underlying natural numbers. -/
def atoms : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na _ => ∅
  | φ & ψ => vocab φ ∪ vocab ψ
  | φ v ψ => vocab φ ∪ vocab ψ
  | □ φ => vocab φ
  | ◇ φ => vocab φ

/-- Literals of a BML Formula. Expressed as underlying natural numbers. -/
def lit : Formula → Finset (Nat ⊕ Nat)
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {Sum.inl n}
  | na n => {Sum.inr n}
  | φ & ψ => lit φ ∪ lit ψ
  | φ v ψ => lit φ ∪ lit ψ
  | □ φ => lit φ
  | ◇ φ => lit φ

/-- Get a fresh variable not occuring in a BML Formula. -/
def freshVar : Formula → Nat
  | ⊤  => 0
  | ⊥  => 0
  | at n  => n + 1
  | na n  => n + 1
  | φ & ψ  => max (freshVar φ) (freshVar ψ)
  | φ v ψ  =>  max (freshVar φ) (freshVar ψ)
  | □ φ  => freshVar φ
  | ◇ φ  => freshVar φ

/-- Fischer-Ladner closure of a BML Formula. -/
def FL : Formula → Sequent
  | ⊥ => {⊥}
  | ⊤ => {⊤}
  | at n => {at n}
  | na n => {na n}
  | φ v ψ => {φ v ψ} ∪ FL φ ∪ FL ψ
  | φ & ψ => {φ & ψ} ∪ FL φ ∪ FL ψ
  | □ φ => {□ φ} ∪ FL φ
  | ◇ φ => {◇ φ} ∪ FL φ

/-! # Lemmas about FL Closure of BML Formulas -/

/-- Fischer-Ladner closure is reflexive. -/
lemma FL_refl {φ : Formula} : φ ∈ FL φ := by cases φ <;> simp [FL]

/-- Fischer-Ladner closure is monotone. -/
lemma FL_mon {φ ψ : Formula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
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

/-! # Basic operations and simp lemmas for Sequents -/
/-- Length of a sequent. -/
def length (Γ : Sequent) : Nat := Finset.sum Γ Formula.length


/- Vocabulary of a sequent. -/
def vocab (Γ : Sequent) : Finset Nat := Finset.biUnion Γ Formula.vocab

/- Given a sequent `Γ`, finds a variable not in `Γ`-/
def freshVar (Γ : Finset Formula) : Nat :=
  if h : Γ = {} then 0 else Finset.max' (Γ.image (Formula.freshVar)) (by
    by_contra con
    simp_all)

def D (Γ : Sequent) : Sequent := Finset.filter (
  fun x => decide (Formula.isDiamond x)) Γ
       ∪ Finset.filterMap Formula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  cases A <;> cases B
  all_goals
  simp_all [Formula.opUnDi])

lemma form_in_seq_size_le {A : Formula} {Δ : Sequent} : A ∈ Δ → A.length ≤ Δ.length :=
  fun A_in ↦ Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 A_in) (by simp)

/-- Fischer-Ladner closure of a sequent. -/
def FL : Sequent → Sequent := fun Δ ↦ Finset.biUnion Δ Formula.FL

/-! # Lemmas about FL Closure of Sequents -/

/- Fischer-Ladner closure is reflexive. -/
lemma FL_refl {Δ : Sequent} : Δ ⊆ FL Δ := by
  simp [Finset.subset_iff, FL]
  intro x x_in
  exact ⟨x, x_in, Formula.FL_refl⟩

/- Fischer-Ladner closure is monotone. -/
lemma FL_mon {Δ Γ : Sequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  simp_all [Finset.subset_iff, FL]
  intro φ ψ ψ_in_Δ φ_sub_ψ
  exact ⟨ψ, Δ_sub_Γ ψ_in_Δ, φ_sub_ψ⟩

/- Fischer-Ladner closure is idempotent. -/
lemma FL_idem {Δ : Sequent} : FL (FL Δ) = FL Δ := by
  simp [Finset.Subset.antisymm_iff]
  constructor
  · simp [Finset.subset_iff, FL]
    intro φ ψ χ χ_in_Δ φ_sub_χ φ_sub_ψ
    exact ⟨χ, χ_in_Δ, by apply Formula.FL_mon φ_sub_χ; simp_all⟩
  · exact FL_mon (FL_refl)


end Sequent

abbrev SplitFormula := Formula ⊕ Formula
abbrev SplitSequent := Finset SplitFormula

/-! # Basic operations and simp lemmas for Split Sequents -/

namespace SplitFormula
def isDiamond : SplitFormula → Bool
  | Sum.inl (◇ _) => true
  | Sum.inr (◇ _) => true
  | _ => false

def opUnDi (φ : SplitFormula) : Option SplitFormula := match φ with
  | Sum.inl (◇ ψ) => Option.some (Sum.inl ψ)
  | Sum.inr (◇ ψ) => Option.some (Sum.inr ψ)
  | _ => none


/- Length of a Split Formula (i.e. length of underlying BML Fornula). -/
def length : (Formula ⊕ Formula) → Nat
  | Sum.inl φ => φ.length
  | Sum.inr φ => φ.length

/- Fischer-Ladner closure of a Split Formula (preserving the formula annotation). -/
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

/-! # Lemmas about FL Closure of Split Formulas -/

lemma FL_SplitFormula_left_eq_FL_Formula_map (φ : Formula) :
  FL (Sum.inl φ) = φ.FL.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]

lemma FL_SplitFormula_right_eq_FL_Formula_map (φ : Formula) :
  FL (Sum.inr φ) = φ.FL.map ⟨Sum.inr, Sum.inr_injective⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]

lemma in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.isLeft := by
  induction φ <;> simp_all [FL] <;> grind

lemma in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.isRight := by
  induction φ <;> simp_all [FL] <;> grind

lemma in_FL_of_in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind

lemma in_FL_of_in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind

/-- Fischer-Ladner Closure is reflexive. -/
lemma FL_refl {φ : SplitFormula} : φ ∈ FL φ := by rcases φ with φ | φ <;> cases φ <;> simp [FL]

/-- Fischer-Ladner Closure is monotone. -/
lemma FL_mon {φ ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
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

/-! # Lemmas about FL Closure of Split Sequents -/
def FL : SplitSequent → SplitSequent := fun Δ ↦ Finset.biUnion Δ SplitFormula.FL

/-- Fischer-Ladner Closure is reflexive. -/
lemma FL_refl {Δ : SplitSequent} : Δ ⊆ FL Δ := by
  simp [Finset.subset_iff, FL]
  constructor
  · exact fun x x_in ↦ Or.inl ⟨x, x_in, SplitFormula.FL_refl⟩
  · exact fun x x_in ↦ Or.inr ⟨x, x_in, SplitFormula.FL_refl⟩

/-- Fischer-Ladner Closure is monotone. -/
lemma FL_mon {Δ Γ : SplitSequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  simp_all [Finset.subset_iff, FL]
  constructor
  all_goals
    intro φ h
    rcases h with h | h
    · have ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩ := h
      exact Or.inl ⟨ψ, Δ_sub_Γ.1 _ ψ_in_Δ, φ_sub_ψ⟩
    · have ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩ := h
      exact Or.inr ⟨ψ, Δ_sub_Γ.2 _ ψ_in_Δ, φ_sub_ψ⟩

/-- Fischer-Ladner Closure is idempotent. -/
lemma FL_idem {Δ : SplitSequent} : FL (FL Δ) = FL Δ := by
  simp [Finset.Subset.antisymm_iff]
  constructor
  · simp [Finset.subset_iff, FL]
    constructor
    all_goals
    intro φ h
    · rcases h with ⟨ψ, ⟨χ, χ_in_Δ, ψ_sub_χ⟩ | ⟨χ, χ_in_Δ, ψ_sub_χ⟩, φ_sub_ψ⟩
                  | ⟨ψ, ⟨χ, χ_in_Δ, ψ_sub_χ⟩ | ⟨χ, χ_in_Δ, ψ_sub_χ⟩, φ_sub_ψ⟩
      · exact Or.inl ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
      · exact Or.inr ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
      · exact Or.inl ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
      · exact Or.inr ⟨χ, χ_in_Δ, by apply SplitFormula.FL_mon ψ_sub_χ; simp_all⟩
  · exact FL_mon FL_refl

/-- □₄⁻¹ operator for Split Sequents. -/
def D (Γ : SplitSequent) : SplitSequent
  := Finset.filter (fun x => decide (SplitFormula.isDiamond x)) Γ
                         ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro φ ψ C C_in_A C_in_B
  rcases φ with φ | φ <;> rcases ψ with ψ | ψ <;> rcases C with C | C
  all_goals
    simp_all
    cases φ <;> cases ψ
    all_goals
      simp_all [SplitFormula.opUnDi])

/-! # Basic operations and simp lemmas for Split Sequents -/

/-- Find underlying Sequent of a Split Sequent. -/
def toSequent (Δ : SplitSequent) : Sequent := Finset.image (Sum.elim id id) Δ

/-- Length of a Split Sequent. -/
def length (Δ : SplitSequent) : Nat := Finset.sum Δ (SplitFormula.length)

@[simp]
lemma opUnDi_eqₗₗ {φ ψ : Formula} : SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inl ψ) ↔ φ = ◇ ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
lemma opUnDi_eqᵣᵣ {φ ψ : Formula} : SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inr ψ) ↔ φ = ◇ ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
lemma opUnDi_eqₗᵣ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inr ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
lemma opUnDi_eqᵣₗ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inl ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
noncomputable def filterLeft : SplitSequent → SplitSequent := @Finset.filter _
  (fun | Sum.inl _ => true | Sum.inr _ => false)
  (fun | Sum.inl _ => isTrue (by simp) | Sum.inr _ => isFalse (by simp))

@[simp]
noncomputable def filterRight : SplitSequent → SplitSequent := @Finset.filter _
  (fun | Sum.inl _ => false | Sum.inr _ => true)
  (fun | Sum.inl _ => isFalse (by simp) | Sum.inr _ => isTrue (by simp))

def left (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getLeft?) (by aesop)
def right (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getRight?) (by aesop)

end SplitSequent

/-! # Properties of Substitutions -/

/-- Substiting `p` with `ψ` in `φ` (`φ[ψ/p]`). --/
def single (n : Nat) (ψ : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at k => if k == n then ψ else at k
  | na k => if k == n then ~ ψ else na k
  | φ₁ & φ₂ => (single n ψ φ₁) & (single n ψ φ₂)
  | φ₁ v φ₂ => (single n ψ φ₁) v (single n ψ φ₂)
  | □ φ => □ (single n ψ φ)
  | ◇ φ => ◇ (single n ψ φ)

/- Single substitution preserves negation. -/
lemma single_neg (n : Nat) (φ ψ : Formula) : single n ψ (~φ) = (~ (single n ψ φ)) := by
  induction φ <;> simp [Formula.neg, single] <;> aesop

/- Single substitution preserves implication. -/
lemma single_imp (n : Nat) (C D E : Formula) : single n C (D ↣ E) = (single n C D) ↣ (single n C E) := by
  simp [single, single_neg]

/- Single substitution preserves bi-implication. -/
lemma single_iff (n : Nat) (C D E : Formula) : single n C (D ⟷ E) = (single n C D) ⟷ (single n C E) := by
  simp [single, single_neg]

@[simp]
lemma single_identity (n : ℕ) (φ : Formula) : (single n (at n) φ) = φ := by
  induction φ <;> simp_all [single]

/-- Simultaneous substitution for `p` meeting criteria `c`. --/
def partial_ {c : Nat → Prop} [DecidablePred c] (σ : Subtype c → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : c n then σ ⟨n, h⟩ else at n
  | na n => if h : c n then ~ σ ⟨n, h⟩ else na n
  | A & B => (partial_ σ A) & (partial_ σ B)
  | A v B => (partial_ σ A) v (partial_ σ B)
  | □ A => □ (partial_ σ A)
  | ◇ A => ◇ (partial_ σ A)

/-- Full substitution of all `p`. -/
def full (σ : Nat → Formula) (A : Formula) : Formula := match A with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => σ n
  | na n => ~ (σ n)
  | A & B => (full σ A) & (full σ B)
  | A v B => (full σ A) v (full σ B)
  | □ A => □ (full σ A)
  | ◇ A => ◇ (full σ A)
termination_by Formula.length A
decreasing_by
  all_goals
  simp [Formula.length]
  try linarith

/-! # Properties of Vocab -/

/- `p` is in the vocabulary of `φ` if and only if `p` is in the vocabulary of `~φ`. -/
@[simp] lemma in_neg_voc_iff {n : Nat} {φ : Formula} : n ∈ (~φ).vocab ↔ n ∈ φ.vocab := by
  induction φ <;> simp_all [Formula.vocab]

lemma in_single_voc (m n : Nat) (φ ψ : Formula) :
  m ∉ φ.vocab → (m ≠ n → m ∉ ψ.vocab) → n ∉ φ.vocab → m ∉ (single n φ ψ).vocab
  := by
    intro mp
    induction ψ <;> simp_all [single, Formula.vocab]
    case atom k =>
      by_cases k = n <;> simp_all [Formula.vocab]; aesop
    case negAtom k =>
      by_cases k = n <;> simp_all [Formula.vocab]
      aesop

lemma not_in_single_voc (n : Nat) (φ ψ : Formula) :
  n ∉ φ.vocab → (single n ψ φ) = φ := by
  intro h
  induction φ <;> simp_all [single, Formula.vocab] <;> aesop

lemma not_in_single_top_voc (n : ℕ) (φ : Formula) : n ∉ (single n ⊤ φ).vocab := by
  induction φ <;> simp_all [single, Formula.vocab]
  all_goals
  rename_i k
  by_cases k = n <;> simp_all [Formula.vocab]; grind

lemma not_in_single_bot_voc (n : ℕ) (φ : Formula) :  n ∉ (single n ⊥ φ).vocab := by
  induction φ <;> simp_all [single, Formula.vocab]
  all_goals
  rename_i k
  by_cases k = n <;> simp_all [Formula.vocab]; grind

lemma in_single_voc' {m n : ℕ} {φ ψ : Formula} : m ∈ (single n φ ψ).vocab → (m ∈ φ.vocab ∧ n ∈ ψ.vocab) ∨ (m ∈ ψ.vocab ∧ m ≠ n) := by
  intro m_in
  induction ψ <;> simp_all [single] <;> try grind [Formula.vocab, in_neg_voc_iff, Formula.instTop, Formula.instBot]


/-! # Some very specific lemmas about Finset.sum

Ideally grind or aesop or some other tactic could sort out these simple helper lemmas, but I could
not figure out how.
-/

lemma sub_add_left {n m l : Nat} : n + m = l → n = l - m := by omega

lemma lt_and_le_imp_add_lt {a b c : ℕ} : b ≤ a → c < b → (a - b) + c < a := by omega

lemma Finset.sum_diff_singleton_lt {α : Type} [DecidableEq α] {A C : Finset α} {b : α} {f : α → Nat}
  : b ∈ A → C.sum f < f b → Finset.sum ((A \ {b}) ∪ C) f < Finset.sum A f := by
  intro b_in_A C_lt_B
  calc
    _ ≤ Finset.sum (A \ {b}) f + Finset.sum C f := by
     simp [sub_add_left $ @Finset.sum_union_inter _ _ (A \ {b}) C _ f _]
    _ = Finset.sum A f - Finset.sum {b} f + Finset.sum C f := by
      simp [sub_add_left $ @Finset.sum_sdiff α Nat {b} A _ f _ (Finset.singleton_subset_iff.2 b_in_A)]
    _ < Finset.sum A f := by
      apply lt_and_le_imp_add_lt
      · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 b_in_A) (by simp))
      · exact C_lt_B
