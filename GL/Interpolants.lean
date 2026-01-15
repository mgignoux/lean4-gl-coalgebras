import GL.Logic
import GL.CoalgebraProof
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.Semantics

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

noncomputable def unencodeVar {𝕏 : Proof} [Fintype 𝕏.X] (n : Nat) (h : n - 𝕏.freeVar < Fintype.card 𝕏.X) : 𝕏.X :=
  (Fintype.equivFin 𝕏.X).symm ⟨n - 𝕏.freeVar, h⟩

lemma encodeVar_inj (𝕏 : Proof) [Fintype 𝕏.X] : Function.Injective (@encodeVar 𝕏 _) := by
  simp [Function.Injective]
  intro x y hyp
  simp [encodeVar, Fin.val_eq_val] at hyp
  exact hyp

lemma encodeVar_inv (𝕏 : Proof) [Fintype 𝕏.X] (x : 𝕏.X) : unencodeVar (encodeVar x) (by simp [encodeVar]) = x := by
  simp [unencodeVar, encodeVar]

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

#check Finset.instInsert
@[simp]
theorem Finset.doubleton_subset_iff {α : Type} [DecidableEq α] {s : Finset α} {a b : α} : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by simp [Finset.subset_iff]

theorem extend_in {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} (Y_sub : Y ⊆ fin_X.elems) (σ : {x : 𝕏.X // x ∈ Y} → Formula) (A : Formula) :
  (∀ y ∈ Y, encodeVar y ∉ Formula.vocab A) → (A = extend Y_sub σ A) := by
  contrapose
  intro hyp
  induction A <;> simp_all [extend, Formula.instBot, Formula.instTop, not_true_eq_false, Formula.vocab, -not_and, not_and_or]
  all_goals
    aesop

theorem encodeVar_in_equation_imp_pred {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {x y : 𝕏.X} :
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

theorem single_preserves_equiv (n : Nat) (C D E : Formula) (h : D ≅ E) : single n C D ≅ single n C E := by
  induction D <;> induction E <;> simp [single] <;> try exact h
  case bottom.atom n =>
    have ⟨𝕏, x, x_prop⟩ := h.2
    have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
    rcases r : (_root_.r 𝕏.α x) <;>
      simp_all [_root_.f, Formula.neg, _root_.fₚ]
  case atom.bottom n =>
    have ⟨𝕏, x, x_prop⟩ := h.1
    have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
    rcases r : (_root_.r 𝕏.α x) <;>
      simp_all [_root_.f, Formula.neg, _root_.fₚ]
  case bottom.neg_atom n =>
    have ⟨𝕏, x, x_prop⟩ := h.2
    have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
    rcases r : (_root_.r 𝕏.α x) <;>
      simp_all [_root_.f, Formula.neg, _root_.fₚ]
  case neg_atom.bottom n =>
    have ⟨𝕏, x, x_prop⟩ := h.1
    have := @_root_.fₚ_sub_f (_root_.r 𝕏.α x)
    rcases r : (_root_.r 𝕏.α x) <;>
      simp_all [_root_.f, Formula.neg, _root_.fₚ]
  all_goals
  sorry

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
      fun n ↦ (single (encodeVar box) ⊤) (partial_ τ (at n)) -- fix this later
    else
      have y_in_Y : ∃ y, y ∈ Y := by by_contra h; apply em_con; apply Finset.eq_empty_of_forall_notMem; simp_all
      have leaf_in_Y := finite_and_no_loop_implies_exists_leaf (fun x ↦ x ∈ Y) y_in_Y.choose y_in_Y.choose_spec loop_con
      let leaf := leaf_in_Y.choose
      let τ := @Solution_strong _ _ (Y \ {leaf}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate
      fun n ↦ (single (encodeVar leaf) (equation leaf)) (partial_ τ (at n))

termination_by Finset.card Y
decreasing_by
  · have box_in : box ∈ Y := box_in_Y.choose_spec.2
    simp [←Finset.card_sdiff_add_card_inter Y {box}, box_in]
    linarith
  · have leaf_in : leaf ∈ Y := leaf_in_Y.choose_spec.1
    simp [←Finset.card_sdiff_add_card_inter Y {leaf}, leaf_in]
    linarith

theorem equiv_help {C D E : Formula} (h : C ≅ D) (g : D = E) : (C ≅ E) := by aesop

set_option maxHeartbeats 1000000
open Classical in
theorem Solution_strong_prop' {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) :
      ∀ n : {n // n ∈ Y.image encodeVar},
          ((Solution_strong Y_sub n = partial_ (Solution_strong Y_sub) (equation (unencodeVar n (helper_1 n.2))))
         ∨ (Solution_strong Y_sub n ≅ partial_ (Solution_strong Y_sub) (equation (unencodeVar n (helper_1 n.2)))))
       ∧ (∀ m : {m // m ∈ Y.image encodeVar}, m.1 ∉ (Solution_strong Y_sub n).vocab) := by

  intro ⟨n, n_in⟩
  unfold Solution_strong
  by_cases em_con : Y = ∅
  · subst em_con
    simp at n_in
  · by_cases loop_con : ∃ y, Relation.TransGen (edge_restr (fun x ↦ x ∈ Y)) y y
    case pos =>
      simp [em_con, loop_con]
      sorry

    case neg =>
      simp [em_con, loop_con]
      have y_in_Y : ∃ y, y ∈ Y := by by_contra h; apply em_con; apply Finset.eq_empty_of_forall_notMem; simp_all
      have leaf_in_Y := finite_and_no_loop_implies_exists_leaf (fun x ↦ x ∈ Y) y_in_Y.choose y_in_Y.choose_spec loop_con

      let τ_prop := @Solution_strong_prop' _ _ (Y \ {leaf_in_Y.choose}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate

      have helper : ¬ encodeVar leaf_in_Y.choose ∈ Finset.image encodeVar (Y \ {leaf_in_Y.choose}) := by
        simp
        intro x x_in hyp con
        apply hyp
        exact encodeVar_inj 𝕏 con

      by_cases n = encodeVar leaf_in_Y.choose
      case pos y_eq_leaf =>
        subst y_eq_leaf
        simp [partial_, helper, single, encodeVar_inv]
        refine ⟨Or.inl ?_, ?_⟩
        · apply partial_const
          intro n n_in
          by_contra h
          simp at h
          have ⟨z, z_prop⟩ := h
          rw [←z_prop.2] at n_in
          have y_z := encodeVar_in_equation_imp_pred n_in
          exact leaf_in_Y.choose_spec.2 _ y_z z_prop.1
        · intro z z_in con
          exact leaf_in_Y.choose_spec.2 z (encodeVar_in_equation_imp_pred con) z_in
      case neg y_ne_leaf =>
        have helper : n ∈ Finset.image encodeVar (Y \ {leaf_in_Y.choose}) := by
          simp
          simp at n_in
          have ⟨n, n_prop⟩ := n_in
          refine ⟨n, ⟨n_prop.1, ?_⟩, n_prop.2⟩
          intro con
          rw [←con] at y_ne_leaf
          exact y_ne_leaf (Eq.symm n_prop.2)
        simp [partial_, helper]
        have ⟨eq_or_equiv, sub_prop⟩ := τ_prop ⟨n, by aesop⟩
        refine ⟨?_, ?_⟩
        · rcases eq_or_equiv with eq | equiv
          · left
            convert @Solution_strong_helper (fun n ↦ n ∈ Finset.image encodeVar (Y \ {leaf_in_Y.choose})) _ (@Solution_strong _ _ (Y \ {leaf_in_Y.choose}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in)) (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose) (equation (unencodeVar n (helper_1 n_in)))
            · simp only [Finset.image_sdiff _ _ (encodeVar_inj 𝕏), Finset.mem_sdiff, Finset.image_singleton, Finset.not_mem_singleton]
              refine ⟨by tauto, ?_⟩
              intro h
              rcases h with h | h <;> simp_all
              exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, rfl⟩
            · sorry
          · right
            have := single_preserves_equiv (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose) _ _ equiv
            apply equiv_help this
            convert @Solution_strong_helper (fun n ↦ n ∈ Finset.image encodeVar (Y \ {leaf_in_Y.choose})) _ (@Solution_strong _ _ (Y \ {leaf_in_Y.choose}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in)) (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose) (equation (unencodeVar n (helper_1 n_in)))
            · simp only [Finset.image_sdiff _ _ (encodeVar_inj 𝕏), Finset.mem_sdiff, Finset.image_singleton, Finset.not_mem_singleton]
              refine ⟨by tauto, ?_⟩
              intro h
              rcases h with h | h <;> simp_all
              exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, rfl⟩
            · sorry
        · intro z z_in
          apply in_single_voc
          · intro con
            exact leaf_in_Y.choose_spec.2 z (encodeVar_in_equation_imp_pred con) z_in
          · intro not_leaf
            exact sub_prop ⟨encodeVar z, by aesop⟩
          · intro con
            exact leaf_in_Y.choose_spec.2 leaf_in_Y.choose (encodeVar_in_equation_imp_pred con) leaf_in_Y.choose_spec.1

termination_by Finset.card Y
decreasing_by
  all_goals
    have leaf_in := leaf_in_Y.choose_spec.1
    simp [←Finset.card_sdiff_add_card_inter Y {leaf_in_Y.choose}, leaf_in]

noncomputable def Interpolant (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Formula → Formula
  := partial_ $ @Solution_strong 𝕏 _ fin_X.elems (by aesop)

lemma eq_chain {α : Type} {a b c d : α} {r : α → α → Prop} (h₁ : r a c) (h₂ : a = b) (h₃ : c = d) : r b d :=
by
  aesop

theorem Interpolant_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    (Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x)
  ∨ (Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x)))
  ∧ (∀ y : 𝕏.X, encodeVar y ∉ (Interpolant 𝕏 (at (encodeVar x))).vocab)
 := by
  unfold Interpolant
  have h : ∀ y : 𝕏.X, encodeVar y ∈ Finset.image encodeVar fin_X.elems := by simp [Fintype.complete]
  have := @Solution_strong_prop' 𝕏 _ fin_X.elems (by aesop) ⟨encodeVar x, by simp [h]⟩
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
  · intro y
    convert this.2 ⟨encodeVar y, by simp [encodeVar, Fintype.complete]⟩
    simp [partial_, h]
