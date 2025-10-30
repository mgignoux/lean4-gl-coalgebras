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

theorem single_neg (n : Nat) (C D : Formula) : single n C (~D) = Formula.neg (single n C D) := by
  induction D <;> simp [Formula.neg, single]
  case neg_atom m =>
    by_cases m = n
    case pos h =>
      simp [h]
      induction C <;> simp [Formula.neg, Formula.instTop, Formula.instBot]
      case and ih1 ih2 => exact ⟨ih1, ih2⟩
      case or ih1 ih2 => exact ⟨ih1, ih2⟩
      case box ih => exact ih
      case diamond ih => exact ih
    case neg h => simp [h]
  all_goals
    aesop

/-- Structure preserving map substituting all atoms meeting a certain criteria p --/
def partial_ {p : Nat → Prop} [DecidablePred p] (σ : Subtype p → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : p n then σ ⟨n, h⟩ else at n
  | na n => if h : p n then ~ σ ⟨n, h⟩ else na n
  | A & B => (partial_ σ A) & (partial_ σ B)
  | A v B => (partial_ σ A) v (partial_ σ B)
  | □ A => □ (partial_ σ A)
  | ◇ A => ◇ (partial_ σ A)

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

noncomputable def unencodeVar {𝕏 : Proof} [Fintype 𝕏.X] (n : Nat) (h : n - 𝕏.freeVar < Fintype.card 𝕏.X) : 𝕏.X :=
  (Fintype.equivFin 𝕏.X).symm ⟨n - 𝕏.freeVar, h⟩

lemma encodeVar_inj (𝕏 : Proof) [Fintype 𝕏.X] : Function.Injective (@encodeVar 𝕏 _) := by
  simp [Function.Injective]
  intro x y hyp
  simp [encodeVar, Fin.val_eq_val] at hyp
  exact hyp

lemma encodeVar_inv (𝕏 : Proof) [Fintype 𝕏.X] (x : 𝕏.X) : unencodeVar (encodeVar x) (by simp [encodeVar]) = x := by sorry

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


inductive ex
  | one : (1 = 1) → ex
  | two : (1 ≠ 1) → ex

def ex_1 (r : ℕ → ex) : ℕ := match _ : (r 1) with
  | .one _ => 1
  | .two _ => 2

theorem ex_2 (r : ℕ → ex) : ex_1 r = 1 ∨ ex_1 r = 2 := by
  rcases r_def : r 1
  unfold ex_1
  rw [r_def]
  simp
  sorry



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
theorem Finset.doubleton_subset_iff {s : Finset Formula} {a b : Formula} : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by sorry

theorem extend_in {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} (Y_sub : Y ⊆ fin_X.elems) (σ : {x : 𝕏.X // x ∈ Y} → Formula) (A : Formula) :
  (∀ y ∈ Y, encodeVar y ∉ Formula.vocab A) → (A = extend Y_sub σ A) := by
  contrapose
  intro hyp
  induction A <;> simp_all [extend, Formula.instBot, Formula.instTop, not_true_eq_false, Formula.vocab, -not_and, not_and_or]
  all_goals
    aesop

theorem encodeVar_in_equation_imp_pred {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {x y : 𝕏.X} :
  encodeVar y ∈ (equation x).vocab → (edge 𝕏.α) x y := by
  simp_all [equation]
  have h := 𝕏.h x
  split <;> try simp [Formula.vocab]
  case h_4 Δ n in_Δ r_def =>
    intro con
    exfalso
    have h : n < 𝕏.freeVar := by
      simp [Proof.freeVar, Sequent.freshVar]
      split
      · sorry
      · sorry

    simp [encodeVar] at con
    linarith
  case h_5 Δ n in_Δ r_def =>
    intro con
    exfalso
    have h : n < 𝕏.freeVar := by sorry
    simp [encodeVar] at con
    linarith
  case h_7 Δ A B in_Δ r_def =>
    split <;> simp_all
    case h_2 p_def =>
      intro mp
      simp [Formula.vocab, encodeVar, ←Fin.ext_iff] at mp
      simp_all [edge]
  case h_8 Δ A B in_Δ r_def =>
    split <;> simp_all
    case h_2 p_def =>
      intro mp
      simp [Formula.vocab, encodeVar, ←Fin.ext_iff] at mp
      simp_all [edge]
  case h_9 Δ A B in_Δ r_def =>
    split <;> simp_all
    case h_3 p_def =>
      intro mp
      simp [Formula.vocab, encodeVar, ←Fin.ext_iff] at mp
      simp_all [edge]
  case h_10 Δ A B in_Δ r_def =>
    split <;> simp_all
    case h_3 p_def =>
      intro mp
      simp [Formula.vocab, encodeVar, ←Fin.ext_iff] at mp
      simp_all [edge]
  case h_11 Δ A in_Δ r_def =>
    split <;> simp_all
    case h_2 p_def =>
      intro mp
      simp [Formula.vocab, encodeVar, ←Fin.ext_iff] at mp
      simp_all [edge]
  case h_12 Δ A in_Δ r_def =>
    split <;> simp_all
    case h_2 p_def =>
      intro mp
      simp [Formula.vocab, encodeVar, ←Fin.ext_iff] at mp
      simp_all [edge]

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


theorem equiv_help {C D E : Formula} (h : C ≅ D) (g : D = E) : (C ≅ E) := by aesop

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

set_option maxHeartbeats 900000
theorem Solution_strong {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) :
    ∃ σ : {n // n ∈ Y.image encodeVar} → Formula,
      ∀ n : {n // n ∈ Y.image encodeVar},
          ((σ n = partial_ σ (equation (unencodeVar n (helper_1 n.2)))) ∨ (σ n ≅ partial_ σ (equation (unencodeVar n (helper_1 n.2)))))
       ∧ (True) -- not a subformula property)
      := by
  -- induction Y using Finset.induction_on --- DONT DO THIS, WE WANT TO SELECT THE ELEMENTS WE REMOVE
  by_cases Y = ∅
  case pos Y_em => -- if empty then vacuously done
    subst Y_em
    simp

  case neg Y_ne =>
    have dec := 𝕏.decidable
    by_cases ∃ y, Relation.TransGen (edge_restr (fun x ↦ x ∈ Y)) y y

    case pos h =>  -- if there is a loop then find the box node which must be in Y
      have ⟨y, y_y⟩ := h
      have ⟨z, z_box, z_in⟩ := exists_box_on_restr_loop y (fun x ↦ x ∈ Y) y_y

      have ⟨τ, τ_prop⟩ := Solution_strong (Y \ {z}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate
      use fun n ↦ (single (encodeVar z) ⊤) (partial_ τ (at n)) -- fix this later

      sorry

    case neg => -- if there is no loop then find a leaf in ↑y

      have ⟨leaf, leaf_in, leaf_prop⟩ : ∃ l ∈ Y, (p 𝕏.α l).toFinset ∩ Y = ∅ := by sorry
      have ⟨τ, τ_prop⟩ := Solution_strong (Y \ {leaf}) (by simp [Finset.subset_iff]; intro _ x_in _; exact Y_sub x_in) -- maybe make seperate
      use fun n ↦ (single (encodeVar leaf) (equation leaf)) (partial_ τ (at n))

      intro ⟨y, y_in⟩
      by_cases y = encodeVar leaf
      case pos y_eq_leaf =>
        subst y_eq_leaf
        refine ⟨Or.inl ?_, by simp⟩
        have  h : ¬ encodeVar leaf ∈ Finset.image encodeVar (Y \ {leaf}) := by sorry
        simp [partial_, h, single, encodeVar_inv]
        apply partial_const
        intro n n_in
        by_contra h
        simp at h
        have ⟨z, z_prop⟩ := h
        rw [←z_prop.2] at n_in
        have y_z := encodeVar_in_equation_imp_pred n_in
        -- this is a contradiction, z is in p α y, and z ∈ Y, so leaf_prop cannot hold
        apply Finset.eq_empty_iff_forall_notMem.1 leaf_prop z
        simp only [Finset.mem_inter, List.mem_toFinset]
        exact ⟨y_z, z_prop.1⟩

      case neg y_ne_leaf =>
        have y_in : y ∈ Finset.image encodeVar (Y \ {leaf}) := by
          simp
          simp at y_in
          have ⟨n, n_prop⟩ := y_in
          refine ⟨n, ⟨n_prop.1, ?_⟩, n_prop.2⟩
          intro con
          rw [←con] at y_ne_leaf
          exact y_ne_leaf (Eq.symm n_prop.2)
        simp only [partial_, y_in, ↓reduceDIte]
        have ⟨eq_or_equiv, prop⟩ := τ_prop ⟨y, by aesop⟩
        rcases eq_or_equiv with eq | equiv -- substitution preserves equality/equivelance
        · refine ⟨Or.inl ?_, by simp⟩ -- recover the other goal here later
          simp only [eq] -- for some reason you can comment this and it still works??
          convert @Solution_strong_helper (fun n ↦ n ∈ Finset.image encodeVar (Y \ {leaf})) _ τ (encodeVar leaf) (equation leaf) (equation (unencodeVar y (helper_1 y_in)))
          · sorry
        · refine ⟨Or.inr ?_, by simp⟩ -- recover the other goal here later
          have := single_preserves_equiv (encodeVar leaf) (equation leaf) _ _ equiv
          apply equiv_help this
          convert @Solution_strong_helper (fun n ↦ n ∈ Finset.image encodeVar (Y \ {leaf})) _ τ (encodeVar leaf) (equation leaf) (equation (unencodeVar y (helper_1 y_in)))
          · sorry

termination_by Finset.card Y
decreasing_by
  · rw [←Finset.card_sdiff_add_card_inter Y {z}]
    cases value : (Y ∩ {z}).card -- roundabout method
    case zero h =>
      exfalso
      simp only [Finset.card_eq_zero, Finset.inter_singleton, z_in, ↓reduceIte, Finset.singleton_ne_empty] at value
    case succ =>
      simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]
  · rw [←Finset.card_sdiff_add_card_inter Y {leaf}]
    cases value : (Y ∩ {leaf}).card -- roundabout method
    case zero h =>
      exfalso
      simp only [Finset.card_eq_zero, Finset.inter_singleton, leaf_in, ↓reduceIte, Finset.singleton_ne_empty] at value
    case succ => simp only [lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true]

-- theorem Solution_strong_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
--   (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) :
--       ∀ y : {x : 𝕏.X // x ∈ Y},
--           (Solution_strong Y Y_sub y.val ≅ extend (Solution_strong Y Y_sub) (equation y.val)) := by
--       --  ∧ (True) -- not a subformula property
--   intro ⟨y, y_in⟩
--   by_cases Y = ∅
--   case pos Y_em =>
--     subst Y_em
--     simp at y_in
--   case neg Y_ne =>
--     by_cases Relation.TransGen (fun y1 y2 ↦ edge 𝕏.α y1 y2 ∧ (y1 ∈ Y ∧ y2 ∈ Y)) y y
--     case pos h =>
--       unfold Solution_strong
--       simp [Y_ne, h]


-- noncomputable def Interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] : 𝕏.X → Formula
--   := fun x ↦ (Solution_strong fin_X.elems (by simp)).choose ⟨x, by sorry⟩
--       -- ∀ x : 𝕏.X, (σ x ≅ extend σ (equation x))
--   --  ∧ ∀ x y : 𝕏.X, P y ∉ σ (P x)  -- how far can we get without this condition?


-- theorem Interpolant_prop (𝕏 : Proof) [fin_X : Fintype 𝕏.X] :
--     ∀ x : 𝕏.X, Interpolant x = extend (@Finset.Subset.rfl _ fin_X.elems) (fun x ↦ Interpolant x.val) (equation x) ∨ (Interpolant x ≅ extend (@Finset.Subset.rfl _ fin_X.elems) (fun x ↦ Interpolant x.val) (equation x))
--   --  ∧ ∀ x y : 𝕏.X, P y ∉ σ (P x)  -- how far can we get without this condition?
--   := by
--   unfold Interpolant
--   have σ_pf := Exists.choose_spec $ Solution_strong fin_X.elems (by simp)
--   intro x
--   have := σ_pf ⟨x, by sorry⟩
--   rcases this with left | right
--   · left
--     exact left
--   · right
--     exact right -- funny thing: exact this doesn't work, but this does :)

theorem Solution_exists {𝕏 : Proof} [fin_X : Fintype 𝕏.X] :
    ∃ σ : {n // n ∈ fin_X.elems.image encodeVar} → Formula,
      ∀ n : {n // n ∈ fin_X.elems.image encodeVar},
          ((σ n = partial_ σ (equation (unencodeVar n (helper_1 n.2)))) ∨ (σ n ≅ partial_ σ (equation (unencodeVar n (helper_1 n.2)))))
       ∧ (True) -- not a subformula property)
  := Solution_strong fin_X.elems subset_rfl

noncomputable def Interpolant (𝕏 : Proof) [fin_X : Fintype 𝕏.X] (φ : Formula) : Formula
  := partial_ (@Solution_exists 𝕏 _).choose φ

lemma eq_chain {α : Type} {a b c d : α} {r : α → α → Prop} (h₁ : r a c) (h₂ : a = b) (h₃ : c = d) : r b d :=
by
  aesop

theorem Interpolant_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    Interpolant 𝕏 (at (encodeVar x)) = Interpolant 𝕏 (equation x) ∨ (Interpolant 𝕏 (at (encodeVar x)) ≅ Interpolant 𝕏 (equation x))
 := by
  have := (@Solution_exists 𝕏 _).choose_spec ⟨encodeVar x, by simp [encodeVar, Fintype.complete]⟩
  unfold Interpolant
  simp [encodeVar_inv] at this
  rcases this with l | r
  · left
    refine eq_chain l ?_ ?_
    · have h : encodeVar x ∈ Finset.image encodeVar fin_X.elems := by sorry
      simp [partial_, h]
    · simp only [and_true, Subtype.forall, Finset.mem_image, forall_exists_index]
  · right
    refine eq_chain r ?_ ?_
    · have h : encodeVar x ∈ Finset.image encodeVar fin_X.elems := by sorry
      simp [partial_, h]
    · simp only [and_true, Subtype.forall, Finset.mem_image, forall_exists_index]

end split
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
