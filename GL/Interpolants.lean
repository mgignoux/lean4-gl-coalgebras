import GL.Logic
-- import GL.CoalgebraProof
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Semantics
import GL.FixedPointTheorem
import GL.AxiomBlame
import GL.SplitCompleteness2

namespace Split

def Proof.Sequent (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Sequent :=
  fin_X.elems.biUnion (fun x ↦ (f (r 𝕏.α x)).image (Sum.elim id id))

def Proof.freeVar (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Nat :=
  Sequent.freshVar (Proof.Sequent 𝕏)

theorem at_in_lt_freeVar {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {n : Nat} (h : at n ∈ 𝕏.Sequent) : n < 𝕏.freeVar := by
  have 𝕏_ne : 𝕏.Sequent ≠ ∅ := by aesop
  simp [Proof.freeVar, Sequent.freshVar, 𝕏_ne]
  apply Nat.lt_of_succ_le
  · apply Finset.le_max'
    simp
    exact ⟨at n, h, by simp [Formula.freshVar]⟩

noncomputable def encodeVar {𝕏 : Proof} [Fintype 𝕏.X] : 𝕏.X → Nat :=
  fun x ↦ 𝕏.freeVar + Fintype.equivFin 𝕏.X x

noncomputable def unencodeVar {𝕏 : Proof} [Fintype 𝕏.X] (n : Nat) (h1 : n - 𝕏.freeVar < Fintype.card 𝕏.X) : 𝕏.X :=
  (Fintype.equivFin 𝕏.X).symm ⟨n - 𝕏.freeVar, h1⟩

lemma encodeVar_inj (𝕏 : Proof) [Fintype 𝕏.X] : Function.Injective (@encodeVar 𝕏 _) := by
  simp [Function.Injective]
  intro x y hyp
  simp [encodeVar, Fin.val_eq_val] at hyp
  exact hyp

@[simp] -- the other version using Function.Injective does not work well with simp
lemma encodeVar_inj' (𝕏 : Proof) [Fintype 𝕏.X] (x y : 𝕏.X) : @encodeVar 𝕏 _ x = @encodeVar 𝕏 _ y ↔ x = y := by
  simp [encodeVar, Fin.val_eq_val]

lemma encodeVar_inv (𝕏 : Proof) [Fintype 𝕏.X] (x : 𝕏.X) : unencodeVar (encodeVar x) (by simp [encodeVar]) = x := by
  simp [unencodeVar, encodeVar]

lemma unencodeVar_inv (𝕏 : Proof) [Fintype 𝕏.X] (n : ℕ) (h1) (h2 : n ≥ 𝕏.freeVar) : encodeVar (@unencodeVar 𝕏 _ n h1) = n := by
  simp [unencodeVar, encodeVar]
  omega

lemma at_in_not_encodeVar {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {n : Nat} (h : at n ∈ 𝕏.Sequent) (x : 𝕏.X) : ¬ encodeVar x = n := by
  have := at_in_lt_freeVar h
  intro con
  subst con
  simp_all [encodeVar]

noncomputable def equation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) : Formula := match r : r 𝕏.α x with
  | RuleApp.topₗ _ _ => ⊥
  | RuleApp.topᵣ _ _ => ⊤
  | RuleApp.axₗₗ _ _ _ => ⊥
  | RuleApp.axₗᵣ _ k _ => na k
  | RuleApp.axᵣₗ _ k _ => at k
  | RuleApp.axᵣᵣ _ _ _ => ⊤
  | RuleApp.orₗ _ _ _ _ => at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.h x; simp [r] at this; aesop)))
  | RuleApp.orᵣ _ _ _ _ => at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.h x; simp [r] at this; aesop)))
  | RuleApp.andₗ _ _ _ _ => at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.h x; simp [r] at this; apply congrArg List.length at this; simp_all [List.length_map]))) v at (encodeVar ((p 𝕏.α x)[1]'(by have := 𝕏.h x; simp [r] at this; apply congrArg List.length at this; simp_all [List.length_map])))
  | RuleApp.andᵣ _ _ _ _ => at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.h x; simp [r] at this; apply congrArg List.length at this; simp_all [List.length_map]))) & at (encodeVar ((p 𝕏.α x)[1]'(by have := 𝕏.h x; simp [r] at this; apply congrArg List.length at this; simp_all [List.length_map])))
  | RuleApp.boxₗ _ _ _ => ◇ at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.h x; simp [r] at this; aesop)))
  | RuleApp.boxᵣ _ _ _ => □ at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.h x; simp [r] at this; aesop)))

theorem helper_1 {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} {n : ℕ} (h : n ∈ Finset.image encodeVar Y) : n - 𝕏.freeVar < Fintype.card 𝕏.X := by
  simp [encodeVar] at h
  have ⟨y, y_in, y_eq⟩ := h
  rw [←y_eq]
  simp

theorem helper_2 {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} {n : ℕ} (h : n ∈ Finset.image encodeVar Y) : unencodeVar n (helper_1 h) ∈ Y := by
  simp [encodeVar] at h
  have ⟨y, y_in, y_eq⟩ := h
  simp [←y_eq, unencodeVar, y_in]

-- apply_substitution
noncomputable def extend {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} (Y_sub : Y ⊆ fin_X.elems) (σ : {x : 𝕏.X // x ∈ Y} → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : n ∈ Y.image encodeVar then σ ⟨unencodeVar n (helper_1 h), helper_2 h⟩ else at n
  | na n => if h : n ∈ Y.image encodeVar then ~ σ ⟨unencodeVar n (helper_1 h), helper_2 h⟩ else na n
  | A & B => (extend Y_sub σ A) & (extend Y_sub σ B)
  | A v B => (extend Y_sub σ A) v (extend Y_sub σ B)
  | □ A => □ (extend Y_sub σ A)
  | ◇ A => ◇ (extend Y_sub σ A)

theorem partial_const {p : Nat → Prop} [DecidablePred p] (σ : Subtype p → Formula) (A : Formula) :
  (∀ n ∈ Formula.vocab A, ¬ p n) → (A = partial_ σ A) := by
  contrapose
  intro hyp
  induction A <;> simp_all [partial_, Formula.instTop, Formula.instBot, not_true_eq_false, Formula.vocab, -not_and, not_and_or]
  all_goals
    aesop
@[simp]
theorem Finset.doubleton_subset_iff {α : Type} [DecidableEq α] {s : Finset α} {a b : α} : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by simp [Finset.subset_iff]

theorem extend_in {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} (Y_sub : Y ⊆ fin_X.elems) (σ : {x : 𝕏.X // x ∈ Y} → Formula) (A : Formula) :
  (∀ y ∈ Y, encodeVar y ∉ Formula.vocab A) → (A = extend Y_sub σ A) := by
  contrapose
  intro hyp
  induction A <;> simp_all [extend, Formula.instBot, Formula.instTop, not_true_eq_false, Formula.vocab, -not_and, not_and_or]
  all_goals
    aesop

theorem encodeVar_in_equation_imp_edge {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {x y : 𝕏.X} :
  encodeVar y ∈ (equation x).vocab → (edge 𝕏.α) x y := by
  unfold equation
  split <;> simp [Formula.vocab, encodeVar, ←Fin.ext_iff, edge]
  case h_4 Δ n in_Δ r =>  -- this is a contradiction because it cannot be = n
    have h : n < 𝕏.freeVar := by
      apply at_in_lt_freeVar
      simp [Proof.Sequent]
      exact ⟨x, fin_X.complete x, by simp [r, f, in_Δ]⟩
    intro con
    linarith
  case h_5 Δ n in_Δ r =>
    have h : n < 𝕏.freeVar := by
      apply at_in_lt_freeVar
      simp [Proof.Sequent]
      exact ⟨x, fin_X.complete x, by simp [r, f, in_Δ]⟩
    intro con
    linarith
  all_goals
    aesop

def SplitSequent.left (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getLeft?) (by aesop)
def SplitSequent.right (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getRight?) (by aesop)

theorem var_in_equation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {x : 𝕏.X} (n : ℕ) :
  n ∈ (equation x).vocab → n ∈ (SplitSequent.left (f (r 𝕏.α x))).vocab ∩ (SplitSequent.right (f (r 𝕏.α x))).vocab
  ∨ ∃ y, encodeVar y = n ∧ (edge 𝕏.α) x y := by
  unfold equation
  split <;> simp [Formula.vocab, encodeVar, edge] <;> try grind
  case h_4 Δ n in_Δ r =>  -- this is a contradiction because it cannot be = n
    simp [r, f, SplitSequent.left, SplitSequent.right, Sequent.vocab]
    grind [Formula.vocab]
  case h_5 Δ n in_Δ r =>
    simp [r, f, SplitSequent.left, SplitSequent.right, Sequent.vocab]
    grind [Formula.vocab]

  -- induction D <;> induction E <;> simp [single] <;> try exact h
  -- case bottom.atom n =>
  --   have ⟨𝕏, x, x_prop⟩ := h.2
  --   have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
  --   rcases r : (_root_.r 𝕏.α x) <;>
  --     simp_all [_root_.f, Formula.neg, _root_.fₚ]
  -- case atom.bottom n =>
  --   have ⟨𝕏, x, x_prop⟩ := h.1
  --   have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
  --   rcases r : (_root_.r 𝕏.α x) <;>
  --     simp_all [_root_.f, Formula.neg, _root_.fₚ]
  -- case bottom.neg_atom n =>
  --   have ⟨𝕏, x, x_prop⟩ := h.2
  --   have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
  --   rcases r : (_root_.r 𝕏.α x) <;>
  --     simp_all [_root_.f, Formula.neg, _root_.fₚ]
  -- case neg_atom.bottom n =>
  --   have ⟨𝕏, x, x_prop⟩ := h.1
  --   have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
  --   rcases r : (_root_.r 𝕏.α x) <;>
  --     simp_all [_root_.f, Formula.neg, _root_.fₚ]
  -- all_goals

theorem Solution_strong_helper {p : Nat → Prop} [DecidablePred p] (σ : Subtype p → Formula) (n : ℕ) {B A : Formula}
  : single n B (partial_ σ A) = @partial_ (fun m ↦ p m ∨ m = n) _ (fun m ↦ single n B (if h : p m then σ ⟨m, h⟩ else at m)) A := by
  induction A
  case top => simp only [partial_, single]
  case bottom => simp only [partial_, single]
  case atom m =>
    simp only [partial_]
    by_cases p m
    case pos pm =>
      simp [pm, ↓reduceDIte]
    case neg not_pm =>
      by_cases m = n
      case pos n_eq_m => simp [n_eq_m, ↓reduceDIte]
      case neg n_ne_m => simp [not_pm, n_ne_m, single]
  case neg_atom m =>
    simp only [partial_]
    by_cases p m
    case pos pm =>
      simp [pm, ↓reduceDIte, single_neg]
    case neg not_pm =>
      by_cases m = n
      case pos n_eq_m =>
        by_cases p n
        case pos pn => simp only [n_eq_m, or_true, ↓reduceDIte, pn, single_neg]
        case neg not_pn => simp only [n_eq_m, or_true, ↓reduceDIte, not_pn, single, BEq.rfl, ↓reduceIte]
      case neg n_ne_m => simp [not_pm, n_ne_m, single]
  case or A B ih1 ih2 => simp [partial_, single, ih1, ih2]
  case and A B ih1 ih2 => simp [partial_, single, ih1, ih2]
  case box A ih => simp [partial_, single, ih]
  case diamond A ih => simp [partial_, single, ih]

noncomputable section
theorem finite_and_no_loop_implies_exists_leaf {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (h : 𝕏.X → Prop) (x : 𝕏.X) (x_sat : h x):
(¬ ∃ y, Relation.TransGen (edge_restr h) y y)
    → ∃ y : 𝕏.X, h y ∧ ∀ z ∈ (p 𝕏.α y), ¬ h z := by
  intro mp
  by_contra con
  simp_all
  let chain : Nat → {x : 𝕏.X // h x} := Nat.rec ⟨x, x_sat⟩ (fun n ih => ⟨(con ih.1 ih.2).choose, (con ih.1 ih.2).choose_spec.2⟩)
  have chain_prop : ∀ n, (edge_restr h) (chain n).1 (chain (n + 1)).1 := by
    intro n
    induction n <;> simp [edge_restr, chain]
    case zero =>
      exact ⟨(Exists.choose_spec (con x x_sat)).1 , x_sat, (Exists.choose_spec (con x x_sat)).2⟩
    case succ n ih =>
      exact ⟨(Exists.choose_spec (con (chain (n + 1)).1 (chain (n + 1)).2)).1, ih.2.2, (Exists.choose_spec (con (chain (n + 1)) ih.2.2)).2⟩
  -- we now have an infinite chain, so we just so it is injective
  have ci_cj : ∀ k n, Relation.TransGen (edge_restr h) (chain k).1 (chain (k + n + 1)).1 := by
    intro m n
    induction n
    case zero => exact Relation.TransGen.single (chain_prop _)
    case succ k ih => exact Relation.TransGen.tail ih (chain_prop (m + k + 1))
  have chain_inj : Function.Injective chain := by
    intro i j con
    rcases Nat.lt_trichotomy i j with lt | eq | gt
    · exfalso
      apply mp (chain i).1
      have ⟨k, diff⟩ := Nat.exists_eq_add_of_lt lt
      convert ci_cj i k
      simp [con, diff]
    · exact eq
    · exfalso
      apply mp (chain i).1
      have ⟨k, diff⟩ := Nat.exists_eq_add_of_lt gt
      convert ci_cj j k
      simp [diff]
  have inf_X := Infinite.of_injective chain chain_inj
  apply inf_X.not_finite
  apply Subtype.finite




open Classical in
def Solution_strong {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  {Y : Finset 𝕏.X} (Y_sub : Y ⊆ fin_X.elems) :
    {n // n ∈ Y.image encodeVar} → Formula :=
    if em_con : Y = ∅ then (fun ⟨n, n_prop⟩ ↦ False.elim (by simp_all)) else
    if loop_con : ∃ y, Relation.TransGen (edge_restr (fun x ↦ x ∈ Y)) y y then
      have box_in_Y := exists_box_on_restr_loop loop_con.choose (fun x ↦ x ∈ Y) loop_con.choose_spec
      let box := box_in_Y.choose
      have τ := @Solution_strong _ _ (Y \ {box}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate
      have box_or_dia : (partial_ τ (equation box)).isBox ∨ (partial_ τ (equation box)).isDiamond := by
        unfold box
        have is_box := box_in_Y.choose_spec.1
        cases r_def : r 𝕏.α box_in_Y.choose <;> simp [r_def] at is_box <;> simp [RuleApp.isBox] at is_box
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isDiamond]
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isBox]
      have ψ := (FixedPointTheorem_simple (partial_ τ (equation box)) (encodeVar box) box_or_dia).choose -- I think this is what we want
      fun n ↦ (single (encodeVar box) ψ) (partial_ τ (at n))
    else
      have y_in_Y : ∃ y, y ∈ Y := by by_contra h; apply em_con; apply Finset.eq_empty_of_forall_notMem; simp_all
      have leaf_in_Y := finite_and_no_loop_implies_exists_leaf (fun x ↦ x ∈ Y) y_in_Y.choose y_in_Y.choose_spec loop_con
      let leaf := leaf_in_Y.choose
      let τ := @Solution_strong _ _ (Y \ {leaf}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate
      fun n ↦ (single (encodeVar leaf) (equation leaf)) (partial_ τ (at n))

termination_by Finset.card Y
decreasing_by
  · have box_in : box ∈ Y := box_in_Y.choose_spec.2.1
    simp [←Finset.card_sdiff_add_card_inter Y {box}, box_in]
    linarith
  · have leaf_in : leaf ∈ Y := leaf_in_Y.choose_spec.1
    simp [←Finset.card_sdiff_add_card_inter Y {leaf}, leaf_in]
    linarith

theorem equiv_help {C D E : Formula} (h : C ≅ D) (g : D = E) : (C ≅ E) := by aesop

-- ∀ m ∈ σ (pₓ), m ∈ (l(x)) ∩ r(x)) ∪ (X / Y) p ∈ ψ [q/φ]

theorem in_single_voc' {m n : ℕ} {φ ψ : Formula} : m ∈ (single n φ ψ).vocab → (m ∈ φ.vocab ∧ n ∈ ψ.vocab) ∨ (m ∈ ψ.vocab ∧ m ≠ n) := by
  intro m_in
  induction ψ <;> simp_all [single] <;> try grind [Formula.vocab, in_neg_voc_iff, Formula.instTop, Formula.instBot]

theorem in_vocab_of_path_left {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y) {n} (n_in : n ∈ (SplitSequent.left (f (r 𝕏.α y))).vocab)
  : n ∈ (SplitSequent.left (f (r 𝕏.α x))).vocab := by
  induction x_y
  case refl => exact n_in
  case tail y z x_y y_z ih =>
    apply ih
    have Xh := 𝕏.h y
    simp [SplitSequent.left, Sequent.vocab] at n_in
    have ⟨φ, φ_in_f, n_in_φ⟩ := n_in
    cases r_def : r 𝕏.α y <;> simp_all [edge] <;> simp [f, SplitSequent.left, Sequent.vocab]
    case andₗ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all
      rcases this with l | l <;> simp [l, fₙ_alternate] at φ_in_f
      all_goals
      · rcases φ_in_f with c1 | c2
        · exact ⟨φ₁ & φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
        · exact ⟨φ, c2.1, n_in_φ⟩
    case andᵣ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all
      rcases this with l | l <;> simp [l, fₙ_alternate] at φ_in_f
      all_goals
        exact ⟨φ, φ_in_f, n_in_φ⟩
    case orₗ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c2 ▸ n_in_φ]⟩
      · exact ⟨φ, c3.1, n_in_φ⟩
    case orᵣ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate]
    case boxₗ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate, SplitSequent.D]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨□φ₁, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ, c2.1.1, n_in_φ⟩
      · exact ⟨◇φ, c3, by simp [Formula.vocab, n_in_φ]⟩
    case boxᵣ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate, SplitSequent.D]
      rcases φ_in_f with c1 | c2
      · exact ⟨φ, c1.1, n_in_φ⟩
      · exact ⟨◇φ, c2, by simp [Formula.vocab, n_in_φ]⟩

theorem in_vocab_of_path_right {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y) {n} (n_in : n ∈ (SplitSequent.right (f (r 𝕏.α y))).vocab)
  : n ∈ (SplitSequent.right (f (r 𝕏.α x))).vocab := by
  induction x_y
  case refl => exact n_in
  case tail y z x_y y_z ih =>
    apply ih
    have Xh := 𝕏.h y
    simp [SplitSequent.right, Sequent.vocab] at n_in
    have ⟨φ, φ_in_f, n_in_φ⟩ := n_in
    cases r_def : r 𝕏.α y <;> simp_all [edge] <;> simp [f, SplitSequent.right, Sequent.vocab]
    case andᵣ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all
      rcases this with l | l <;> simp [l, fₙ_alternate] at φ_in_f
      all_goals
      · rcases φ_in_f with c1 | c2
        · exact ⟨φ₁ & φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
        · exact ⟨φ, c2.1, n_in_φ⟩
    case andₗ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all
      rcases this with l | l <;> simp [l, fₙ_alternate] at φ_in_f
      all_goals
        exact ⟨φ, φ_in_f, n_in_φ⟩
    case orᵣ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c2 ▸ n_in_φ]⟩
      · exact ⟨φ, c3.1, n_in_φ⟩
    case orₗ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate]
    case boxᵣ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate, SplitSequent.D]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨□φ₁, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ, c2.1.1, n_in_φ⟩
      · exact ⟨◇φ, c3, by simp [Formula.vocab, n_in_φ]⟩
    case boxₗ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all [fₙ_alternate, SplitSequent.D]
      rcases φ_in_f with c1 | c2
      · exact ⟨φ, c1.1, n_in_φ⟩
      · exact ⟨◇φ, c2, by simp [Formula.vocab, n_in_φ]⟩

theorem encodeVar_eq {𝕏 : Proof} {Fin_X : Fintype 𝕏.X} {x : 𝕏.X} {n : ℕ} {h1} {h2 : n ≥ 𝕏.freeVar} : encodeVar x = n ↔ x = unencodeVar n h1 := by
  constructor
  · intro mp
    subst mp
    simp [encodeVar_inv]
  · intro mpp
    subst mpp
    apply unencodeVar_inv
    exact h2

set_option maxHeartbeats 1000000 in
open Classical in
theorem Solution_strong_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) :
      ∀ n : {n // n ∈ Y.image encodeVar},
          ((Solution_strong Y_sub n = partial_ (Solution_strong Y_sub) (equation (unencodeVar n (helper_1 n.2))))
         ∨ (Solution_strong Y_sub n ≅ partial_ (Solution_strong Y_sub) (equation (unencodeVar n (helper_1 n.2)))))
       ∧ (∀ m ∈ (Solution_strong Y_sub n).vocab, m ∈ ((SplitSequent.left (f (r 𝕏.α (unencodeVar n (helper_1 n.2))))).vocab ∩ (SplitSequent.right (f (r 𝕏.α (unencodeVar n (helper_1 n.2))))).vocab) ∪ (fin_X.elems.image encodeVar \ Y.image encodeVar))
       ∧ (∀ y : 𝕏.X, encodeVar y ∈ (partial_ (Solution_strong Y_sub) (at n)).vocab → (Relation.ReflTransGen (edge 𝕏.α)) (unencodeVar n (helper_1 n.2)) y)
       := by
  unfold Solution_strong
  intro ⟨n, n_in⟩
  by_cases em_con : Y = ∅
  · subst em_con
    simp at n_in
  · by_cases loop_con : ∃ y, Relation.TransGen (edge_restr (fun x ↦ x ∈ Y)) y y
    case pos =>
      simp [em_con, loop_con]
      have box_in_Y := exists_box_on_restr_loop loop_con.choose (fun x ↦ x ∈ Y) loop_con.choose_spec
      have Z_sub : Y \ {box_in_Y.choose} ⊆ Fintype.elems := by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in
      let τ_prop := @Solution_strong_prop _ _ (Y \ {box_in_Y.choose}) Z_sub -- maybe make seperate
      have box_or_dia : (partial_ (Solution_strong Z_sub) (equation box_in_Y.choose)).isBox ∨ (partial_ (Solution_strong Z_sub) (equation box_in_Y.choose)).isDiamond := by
        have is_box := box_in_Y.choose_spec.1
        cases r_def : r 𝕏.α box_in_Y.choose <;> simp [r_def] at is_box <;> simp [RuleApp.isBox] at is_box
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isDiamond]
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isBox]
      have fpt := (FixedPointTheorem_simple (partial_ (Solution_strong Z_sub) (equation box_in_Y.choose)) (encodeVar box_in_Y.choose) box_or_dia)
      have const := partial_const (Solution_strong Z_sub) (at (encodeVar box_in_Y.choose)) (by
        simp [Formula.vocab, Finset.mem_singleton, forall_eq])
      have ⟨z, p_eq, z_in, box_z⟩ : ∃ z, p 𝕏.α box_in_Y.choose = [z] ∧ z ∈ Y ∧ z ∈ p 𝕏.α box_in_Y.choose := by
        have is_box := box_in_Y.choose_spec.1
        have Xh := 𝕏.h box_in_Y.choose
        cases r_def : r 𝕏.α box_in_Y.choose <;> simp [r_def] at is_box <;> simp [RuleApp.isBox] at is_box <;> simp [r_def] at Xh
        all_goals
        refine ⟨Xh.choose, Xh.choose_spec.1, ?_, ?_⟩
        · by_cases box_is_z : box_in_Y.choose = Xh.choose
          · simp [←box_is_z]
            exact box_in_Y.choose_spec.2.1
          · have ⟨d, box_d⟩ : ∃ d, Relation.TransGen (edge_restr fun x ↦ x ∈ Y) box_in_Y.choose d := by
              exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.2⟩
            cases box_d using Relation.TransGen.head_induction_on
            case neg.single box_d =>
              unfold edge_restr edge at box_d
              convert box_d.2.2
              have := Xh.choose_spec.1
              rw [this] at box_d
              exact Eq.symm $ List.mem_singleton.1 box_d.1
            case neg.head box_d heq =>
              unfold edge_restr edge at box_d
              convert box_d.2.2
              have := Xh.choose_spec.1
              rw [this] at box_d
              exact Eq.symm $ List.mem_singleton.1 box_d.1
        · have := Xh.choose_spec.1
          convert List.mem_singleton_self Xh.choose
      have equation_eq : equation box_in_Y.choose = □ (at (encodeVar z)) ∨ equation box_in_Y.choose = ◇ (at (encodeVar z)) := by
        have is_box := box_in_Y.choose_spec.1
        unfold equation
        split <;> rename_i r_def <;> simp [r_def] at is_box <;> simp [RuleApp.isBox] at is_box <;> simp [p_eq]
      by_cases n = encodeVar box_in_Y.choose
      case pos y_eq_box =>
        subst y_eq_box
        refine ⟨?_, ?_, ?_⟩
        · right -- double check this
          simp [partial_, single, encodeVar_inv]
          have h : fpt.choose ≅ (single (encodeVar box_in_Y.choose) fpt.choose (partial_ (Solution_strong Z_sub) (equation box_in_Y.choose))) := equiv_iff_sem_equiv.1 fpt.choose_spec.2.1
          convert h using 1
          rcases equation_eq with c | c
          all_goals
            simp [c, partial_, single, z_in]
        · simp [←const, single]
          intro m m_in_fpt
          have m_in_eq := fpt.choose_spec.2.2 m_in_fpt
          rcases equation_eq with c | c
          all_goals
            simp [c, partial_, Formula.vocab] at m_in_eq
            by_cases box_is_z : z = box_in_Y.choose
            · exfalso
              subst box_is_z
              simp [Formula.vocab] at m_in_eq
              subst m_in_eq
              exact fpt.choose_spec.1 m_in_fpt
            · simp [z_in, box_is_z] at m_in_eq
              have m_in_ih := (τ_prop ⟨encodeVar z, by simp [z_in, box_is_z]⟩).2.1 _ m_in_eq
              simp at m_in_ih
              rcases m_in_ih with m_in_seq | m_in_var
              · refine Or.inl ⟨?_, ?_⟩
                · convert @in_vocab_of_path_left 𝕏 box_in_Y.choose z (Relation.ReflTransGen.single box_z) m (by convert m_in_seq.1; simp [encodeVar_inv])
                  simp [encodeVar_inv]
                · convert @in_vocab_of_path_right 𝕏 box_in_Y.choose z (Relation.ReflTransGen.single box_z) m (by convert m_in_seq.2; simp [encodeVar_inv])
                  simp [encodeVar_inv]
              · refine Or.inr ⟨m_in_var.1, ?_⟩
                · intro x x_in con
                  subst con
                  apply m_in_var.2 x x_in
                  intro con
                  subst con
                  apply fpt.choose_spec.1 m_in_fpt
                  rfl
        · intro y
          simp [partial_, single, n_in, encodeVar_inv]
          intro mp
          have mp := fpt.choose_spec.2.2 mp
          rcases equation_eq with c | c
          all_goals
            by_cases box_is_z : z = box_in_Y.choose
            · subst box_is_z
              simp [c, partial_, Formula.vocab] at mp
              subst mp
              exact Relation.ReflTransGen.refl
            · simp [c, partial_, Formula.vocab, z_in, box_is_z] at mp
              have z_y := (τ_prop ⟨encodeVar z, by simp_all⟩).2.2 y (by convert mp; simp [partial_, z_in, box_is_z])
              simp [encodeVar_inv] at z_y
              apply Relation.ReflTransGen.head box_z z_y
      case neg y_ne_box =>
        have n_in' : n ∈ Finset.image encodeVar (Y \ {box_in_Y.choose}) := by
          simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
          refine ⟨unencodeVar n (helper_1 n_in), ⟨helper_2 n_in, ?_⟩, ?_⟩
          · intro con
            apply y_ne_box
            simp [←con, encodeVar, unencodeVar]
            have := helper_1 n_in
            simp at n_in
            have ⟨y, y_in, y_eq⟩ := n_in
            subst y_eq
            simp [encodeVar]
          · apply unencodeVar_inv
            simp at n_in
            have ⟨y, y_in, y_eq⟩ := n_in
            subst y_eq
            simp [encodeVar]
        have ⟨eq_or_equiv, vocab, path⟩ := τ_prop ⟨n, n_in'⟩
        refine ⟨?_, ?_, ?_⟩
        · rcases eq_or_equiv with eq | equiv
          · left
            simp [partial_, n_in', eq]
            convert @Solution_strong_helper _ _ (Solution_strong Z_sub) (encodeVar box_in_Y.choose) fpt.choose (equation (unencodeVar n (helper_1 n_in)))
            · simp
              constructor
              · intro ⟨y, y_in, y_eq⟩
                subst y_eq
                by_cases y_is_box : y = box_in_Y.choose
                · subst y_is_box
                  right
                  rfl
                · left
                  use y
              · intro mpp
                rcases mpp with ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ | x_eq
                · subst y_eq
                  use y
                · subst x_eq
                  exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, rfl⟩
            · simp
              rename_i heq
              constructor
              · intro mpp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
                · simp
                  constructor
                  · intro mp
                    rcases mp with l | r
                    · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                    · exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, Eq.symm r⟩
                  · intro mpp
                    have ⟨y, y_in_Y, y_eq⟩ := mpp
                    subst y_eq
                    by_cases h : y = box_in_Y.choose
                    · right
                      subst h
                      rfl
                    · left
                      use y
                · exact HEq.symm heq
              · intro mp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
          · right
            simp [partial_, n_in']
            have := single_preserves_equiv (encodeVar box_in_Y.choose) _ _ fpt.choose equiv
            apply equiv_help this

            convert @Solution_strong_helper _ _ (Solution_strong Z_sub) (encodeVar box_in_Y.choose) fpt.choose (equation (unencodeVar n (helper_1 n_in)))
            · simp
              constructor
              · intro mp
                have ⟨y, y_in_Y, y_eq⟩ := mp
                subst y_eq
                by_cases h : y = box_in_Y.choose
                · right
                  subst h
                  rfl
                · left
                  use y
              · intro mpp
                rcases mpp with l | r
                · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                · exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, Eq.symm r⟩
            · simp
              rename_i heq
              constructor
              · intro mpp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
                · simp
                  constructor
                  · intro mp
                    rcases mp with l | r
                    · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                    · exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, Eq.symm r⟩
                  · intro mpp
                    have ⟨y, y_in_Y, y_eq⟩ := mpp
                    subst y_eq
                    by_cases h : y = box_in_Y.choose
                    · right
                      subst h
                      rfl
                    · left
                      use y
                · exact HEq.symm heq
              · intro mp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
        · intro m m_in
          rcases in_single_voc' m_in with ⟨m_in_fpt, box_in_τ⟩ | ⟨m_in_τ, m_not_box⟩
          · have m_in_eq := fpt.choose_spec.2.2 m_in_fpt
            rcases equation_eq with c | c
            all_goals
            by_cases z_is_box : z = box_in_Y.choose
            · exfalso
              simp [c, partial_, Formula.vocab, z_is_box] at m_in_eq
              subst m_in_eq
              apply fpt.choose_spec.1
              exact m_in_fpt
            · simp [partial_, n_in'] at m_in
              simp [c, partial_, Formula.vocab, z_is_box, z_in] at m_in_eq
              have m_in := (τ_prop ⟨encodeVar z, by simp [z_in, z_is_box]⟩).2.1 m m_in_eq
              simp at m_in
              rcases m_in with m_in_seq | m_in_var
              · refine Or.inl ⟨?_, ?_⟩
                · apply @in_vocab_of_path_left 𝕏 (unencodeVar n (helper_1 n_in)) z ?_ m (by convert m_in_seq.1; simp [encodeVar_inv])
                  exact Relation.ReflTransGen.tail (path box_in_Y.choose box_in_τ) box_z
                · apply @in_vocab_of_path_right 𝕏 (unencodeVar n (helper_1 n_in)) z ?_ m (by convert m_in_seq.2; simp [encodeVar_inv])
                  exact Relation.ReflTransGen.tail (path box_in_Y.choose box_in_τ) box_z
              · refine Or.inr ⟨m_in_var.1, ?_⟩
                · intro x x_in con
                  subst con
                  apply m_in_var.2 x x_in
                  intro con
                  subst con
                  apply fpt.choose_spec.1 m_in_fpt
                  rfl
          · simp [partial_, n_in'] at m_in_τ
            have ih := vocab m m_in_τ
            simp at ih
            rcases ih with ih1 | ih2
            · exact Or.inl ih1
            · refine Or.inr ⟨ih2.1, ?_⟩
              intro x x_in con
              apply ih2.2 x x_in ?_ con
              intro eq
              subst eq
              subst con
              apply m_not_box
              rfl
        · simp [partial_, n_in, n_in']
          simp [partial_, n_in'] at path
          intro y mp
          rcases in_single_voc' mp with ⟨y_in_fpt, box_in_τ⟩ | ⟨y_in_τ, y_not_box⟩
          · have y_in_eq := fpt.choose_spec.2.2 y_in_fpt
            rcases equation_eq with c | c
            all_goals
              simp [c, partial_, Formula.vocab, z_in] at y_in_eq
              by_cases z_is_box : z = box_in_Y.choose
              · subst z_is_box
                simp [Formula.vocab] at y_in_eq
                subst y_in_eq
                exact path box_in_Y.choose box_in_τ
              · simp [z_is_box] at y_in_eq
                have := (τ_prop ⟨encodeVar z, by simp [z_in, z_is_box]⟩).2.2
                simp [partial_, z_in, z_is_box, encodeVar_inv] at this
                apply Relation.ReflTransGen.trans ?_ (this y y_in_eq)
                exact Relation.ReflTransGen.tail (path box_in_Y.choose box_in_τ) box_z
          · exact path y y_in_τ
    case neg =>
      simp [em_con, loop_con]
      have y_in_Y : ∃ y, y ∈ Y := by by_contra h; apply em_con; apply Finset.eq_empty_of_forall_notMem; simp_all
      have leaf_in_Y := finite_and_no_loop_implies_exists_leaf (fun x ↦ x ∈ Y) y_in_Y.choose y_in_Y.choose_spec loop_con
      have Z_sub : Y \ {leaf_in_Y.choose} ⊆ Fintype.elems := by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in
      let τ_prop := @Solution_strong_prop _ _ (Y \ {leaf_in_Y.choose}) Z_sub -- maybe make seperate

      have const := partial_const (Solution_strong Z_sub) (at (encodeVar leaf_in_Y.choose)) (by
        simp [Formula.vocab, Finset.mem_singleton, forall_eq])

      by_cases n = encodeVar leaf_in_Y.choose
      case pos y_eq_box =>
        subst y_eq_box
        refine ⟨?_, ?_, ?_⟩
        · left
          simp [partial_, single, encodeVar_inv]
          apply partial_const
          intro n n_in
          by_contra h
          simp at h
          have ⟨z, z_prop⟩ := h
          rw [←z_prop.2] at n_in
          have y_z := encodeVar_in_equation_imp_edge n_in
          exact leaf_in_Y.choose_spec.2 _ y_z z_prop.1

        · simp [←const, single]
          intro m m_in_eq
          rcases var_in_equation _ m_in_eq with ax_or | desc
          · left
            simp at ax_or
            have convert_helper := encodeVar_inv 𝕏 leaf_in_Y.choose
            convert ax_or
          · right
            have ⟨y, y_eq, box_y⟩ := desc
            subst y_eq
            refine ⟨⟨y, fin_X.complete y, rfl⟩, ?_⟩
            intro x x_in eq
            have := @encodeVar_inj 𝕏 fin_X x y eq
            subst this
            exact leaf_in_Y.choose_spec.2 x box_y x_in
        · intro y
          simp [partial_, single, n_in]
          intro mp
          convert Relation.ReflTransGen.single (encodeVar_in_equation_imp_edge mp)
          simp [encodeVar_inv]
      case neg y_ne_box =>
        have n_in' : n ∈ Finset.image encodeVar (Y \ {leaf_in_Y.choose}) := by
          simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
          refine ⟨unencodeVar n (helper_1 n_in), ⟨helper_2 n_in, ?_⟩, ?_⟩
          · intro con
            apply y_ne_box
            simp [←con, encodeVar, unencodeVar]
            have := helper_1 n_in
            simp at n_in
            have ⟨y, y_in, y_eq⟩ := n_in
            subst y_eq
            simp [encodeVar]
          · apply unencodeVar_inv
            simp at n_in
            have ⟨y, y_in, y_eq⟩ := n_in
            subst y_eq
            simp [encodeVar]
        have ⟨eq_or_equiv, vocab, path⟩ := τ_prop ⟨n, n_in'⟩
        refine ⟨?_, ?_, ?_⟩
        · rcases eq_or_equiv with eq | equiv
          · left
            simp [partial_, n_in', eq]
            convert @Solution_strong_helper _ _ (Solution_strong Z_sub) (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose) (equation (unencodeVar n (helper_1 n_in)))
            · simp
              constructor
              · intro mp
                have ⟨y, y_in_Y, y_eq⟩ := mp
                subst y_eq
                by_cases h : y = leaf_in_Y.choose
                · right
                  subst h
                  rfl
                · left
                  use y
              · intro mpp
                rcases mpp with l | r
                · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
            · simp
              rename_i heq
              constructor
              · intro mpp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
                · simp
                  constructor
                  · intro mp
                    rcases mp with l | r
                    · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                    · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
                  · intro mpp
                    have ⟨y, y_in_Y, y_eq⟩ := mpp
                    subst y_eq
                    by_cases h : y = leaf_in_Y.choose
                    · right
                      subst h
                      rfl
                    · left
                      use y
                · exact HEq.symm heq
              · intro mp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
          · right
            simp [partial_, n_in']
            have := single_preserves_equiv (encodeVar leaf_in_Y.choose) _ _ (equation leaf_in_Y.choose) equiv
            apply equiv_help this

            convert @Solution_strong_helper _ _ (Solution_strong Z_sub) (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose) (equation (unencodeVar n (helper_1 n_in)))
            · simp
              constructor
              · intro mp
                have ⟨y, y_in_Y, y_eq⟩ := mp
                subst y_eq
                by_cases h : y = leaf_in_Y.choose
                · right
                  subst h
                  rfl
                · left
                  use y
              · intro mpp
                rcases mpp with l | r
                · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
            · simp
              rename_i heq
              constructor
              · intro mpp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq
                · simp
                  constructor
                  · intro mp
                    rcases mp with l | r
                    · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
                    · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
                  · intro mpp
                    have ⟨y, y_in_Y, y_eq⟩ := mpp
                    subst y_eq
                    by_cases h : y = leaf_in_Y.choose
                    · right
                      subst h
                      rfl
                    · left
                      use y
                · exact HEq.symm heq
              · intro mp
                have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
                refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
                convert y_eq

        · intro m m_in
          rcases in_single_voc' m_in with ⟨m_in_eq, leaf_in_τ⟩ | ⟨m_in_τ, m_not_box⟩
          · rcases var_in_equation _ m_in_eq with ax_or | desc
            · left
              have un_y := path leaf_in_Y.choose leaf_in_τ
              simp at ax_or
              exact ⟨in_vocab_of_path_left un_y ax_or.1, in_vocab_of_path_right un_y ax_or.2⟩
            · right
              have ⟨y, y_eq, leaf_y⟩ := desc
              subst y_eq
              refine ⟨⟨y, fin_X.complete y, rfl⟩, ?_⟩
              intro x x_in eq
              have := @encodeVar_inj 𝕏 fin_X x y eq
              subst this
              exact leaf_in_Y.choose_spec.2 x leaf_y x_in
          · simp [partial_, n_in'] at m_in_τ
            have ih := vocab m m_in_τ
            simp at ih
            rcases ih with ih1 | ih2
            · exact Or.inl ih1
            · refine Or.inr ⟨ih2.1, ?_⟩
              intro x x_in con
              apply ih2.2 x x_in ?_ con
              intro eq
              subst eq
              subst con
              apply m_not_box
              rfl
        · simp [partial_, n_in, n_in']
          simp [partial_, n_in'] at path
          intro y mp
          rcases in_single_voc' mp with ⟨y_in_eq, leaf_in_τ⟩ | ⟨y_in_τ, y_not_box⟩
          · exact Relation.ReflTransGen.tail (path leaf_in_Y.choose leaf_in_τ) (encodeVar_in_equation_imp_edge y_in_eq)
          · exact path y y_in_τ
termination_by Finset.card Y
decreasing_by
  · have box_in : box_in_Y.choose ∈ Y := box_in_Y.choose_spec.2.1
    simp [←Finset.card_sdiff_add_card_inter Y {box_in_Y.choose}, box_in]
  · have leaf_in : leaf_in_Y.choose ∈ Y := leaf_in_Y.choose_spec.1
    simp [←Finset.card_sdiff_add_card_inter Y {leaf_in_Y.choose}, leaf_in]

noncomputable def Interpolant (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Formula → Formula
  := partial_ $ @Solution_strong 𝕏 _ fin_X.elems (by aesop)

lemma eq_chain {α : Type} {a b c d : α} {r : α → α → Prop} (h₁ : r a c) (h₂ : a = b) (h₃ : c = d) : r b d :=
by
  aesop

theorem Interpolant_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    (Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
  ∨ (Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x)))
  ∧ (Interpolant 𝕏 (at (encodeVar x))).vocab ⊆ ((SplitSequent.left (f (r 𝕏.α x))).vocab ∩ (SplitSequent.right (f (r 𝕏.α x))).vocab)
 := by
  unfold Interpolant
  have h : ∀ y : 𝕏.X, encodeVar y ∈ Finset.image encodeVar fin_X.elems := by simp [Fintype.complete]
  have := @Solution_strong_prop 𝕏 _ fin_X.elems (by aesop) ⟨encodeVar x, by simp [h]⟩
  refine ⟨?_, ?_⟩
  · rcases this.1 with l | r
    · left
      refine eq_chain l ?_ ?_
      · simp [partial_, h]
      · apply congrArg₂
        · rfl
        · simp [encodeVar_inv]
    · right
      refine eq_chain r ?_ ?_
      · simp [partial_, h]
      · apply congrArg₂
        · rfl
        · simp [encodeVar_inv]
  · have h : encodeVar x ∈ Finset.image encodeVar fin_X.elems := by simp; exact fin_X.complete _
    simp [partial_, h]
    intro m m_in
    have := this.2.1 m m_in
    simp at this
    convert this
    simp [encodeVar_inv]

#axiom_blame Interpolant_prop
