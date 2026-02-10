import GL.Semantics
import GL.AxiomBlame

def Formula.modalized (n : Nat) : Formula → Bool
  | ⊤ => False
  | ⊥ => False
  | at _ => False
  | na _ => False
  | φ & ψ => modalized n φ ∧ modalized n ψ
  | φ v ψ => modalized n φ ∧ modalized n ψ
  | □ _ => True
  | ◇ _ => True

axiom FixedPointTheorem (φ : Formula) (n : ℕ) (n_modal_in_φ : φ.modalized n) : ∃ (ψ : Formula),
  n ∉ Formula.vocab ψ ∧ sem_equiv ψ (single n ψ φ) ∧ Formula.vocab ψ ⊆ Formula.vocab φ

theorem not_in_single_voc (n : Nat) (φ ψ : Formula) : n ∉ φ.vocab → (single n ψ φ) = φ := by
  intro h
  induction φ <;> simp_all [single, Formula.instBot, Formula.instTop, Formula.vocab] <;> aesop

@[simp]
theorem single_identity (n : ℕ) (φ : Formula) : (single n (at n) φ) = φ := by
  induction φ <;> simp_all [single, Formula.instBot, Formula.instTop]

theorem Semantic_Substitution_Lemma {α : Type} (M : Model α) (u : α) (n : ℕ) (φ ψ χ : Formula)  :
  Evaluate ⟨M, u⟩ (⊡ (φ ⟷ ψ)) → Evaluate ⟨M, u⟩ ((single n φ χ) ⟷ (single n ψ χ)) := by
    intro mp
    induction χ generalizing u
    case bottom => simp [single]
    case top => simp [single]
    case atom k =>
      by_cases eq : k = n
      · simp_all [single]
      · simp [single, eq]
        grind
    case neg_atom k =>
      by_cases eq : k = n
      · simp_all [single]
        grind
      · simp_all [single]
        grind
    case and ih1 ih2 =>
      simp_all [single]
      grind
    case or ih1 ih2 =>
      simp_all [single]
      grind
    case box χ ih1 =>
      constructor <;> simp_all only [Evaluate_and, Evaluate_imp, single]
      · intro h w u_w
        have := mp.2 w u_w
        simp only [Evaluate_and, Evaluate_imp] at this
        exact ((ih1 w) ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).1 (h w u_w)
      · intro h w u_w
        have := mp.2 w u_w
        simp only [Evaluate_and, Evaluate_imp] at this
        exact ((ih1 w) ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).2 (h w u_w)
    case diamond χ ih =>
      constructor <;> simp_all only [Evaluate_and, Evaluate_imp, single]
      · intro ⟨w, u_w, h⟩
        refine ⟨w, u_w, ?_⟩
        have := mp.2 w u_w
        simp only [Evaluate_and, Evaluate_imp] at this
        exact (ih w ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).1 h
      · intro ⟨w, u_w, h⟩
        refine ⟨w, u_w, ?_⟩
        have := mp.2 w u_w
        simp only [Evaluate_and, Evaluate_imp] at this
        exact (ih w ⟨this, fun o w_o ↦ mp.2 o (M.trans u_w w_o)⟩).2 h

def Formula.positive : Formula → ℕ → Prop
  | ⊤, _ => True
  | ⊥, _ => True
  | at _, _ => True
  | na k, n => if k = n then False else True
  | φ & ψ, n => Formula.positive φ n ∧ Formula.positive ψ n
  | φ v ψ, n => Formula.positive φ n ∧ Formula.positive ψ n
  | □ φ, n => Formula.positive φ n
  | ◇ φ, n => Formula.positive φ n

-- theorem single_positive_semantic_imp (φ : Formula) (n : Nat) (pos : φ.positive n): ⊨ φ ↣ single n ⊤ φ := by
--   simp only [Formula.isValid, Evaluate_imp]
--   intro α M u u_φ
--   induction φ generalizing u <;> simp_all [single, Formula.positive] <;> aesop

lemma GL_eval_not_box_prop {α : Type} {M : Model α} {u : α} {φ : Formula} :
  ¬ Evaluate ⟨M, u⟩ (□ φ) → ∃ w, M.R u w ∧ Evaluate ⟨M, w⟩ (□ φ) ∧ ¬ Evaluate ⟨M, w⟩ φ := by
  intro mp
  simp at mp
  have ⟨w, u_w, w1⟩ := mp
  by_cases w2 : Evaluate (M, w) (□φ)
  · exact ⟨w, u_w, w2, w1⟩
  · have ⟨o, w_o, o1⟩ := GL_eval_not_box_prop w2
    exact ⟨o, M.trans u_w w_o, o1⟩
termination_by
  M.con_wf.wrap u
decreasing_by
  simp [WellFounded.wrap, Function.swap, u_w]


theorem FPT_box_helper (φ : Formula) (n : Nat)
  : ⊨ (⊡ (at n ⟷ single n ⊤ (□ φ))) ↣ (at n ⟷ □ φ) := by
  simp only [Formula.isValid, Evaluate_imp, Evaluate_and]
  intro α M u ⟨⟨mp1, mp2⟩, mp3⟩
  constructor
  · intro mp
    have claim : Evaluate ⟨M, u⟩ (⊡ (at n ⟷ ⊤)) := by
      simp
      refine ⟨mp, fun w u_w ↦ ?_⟩
      have := (mp3 w u_w).2
      simp only [Evaluate_imp] at this
      apply this
      intro o w_o
      exact mp1 mp o (M.trans u_w w_o)
    have := Semantic_Substitution_Lemma M u n (at n) (⊤) (□ φ) claim
    simp only [Evaluate_and, Evaluate_imp, single, single_identity] at this
    apply this.2 (mp1 mp)
  · intro mpp
    by_contra con
    have h1 : ¬ Evaluate (M, u) (single n ⊤ (□φ)) := by simp_all
    have ⟨w, u_w, w1, w2⟩ := GL_eval_not_box_prop h1
    have claim : Evaluate ⟨M, w⟩ (⊡ (at n ⟷ ⊤)) := by
      simp
      have mp3_w := mp3 w u_w
      simp only [Evaluate_and, Evaluate_imp] at mp3_w
      refine ⟨mp3_w.2 w1, fun o w_o ↦ ?_⟩
      have mp3_o := mp3 o (M.trans u_w w_o)
      simp only [Evaluate_and, Evaluate_imp] at mp3_o
      exact mp3_o.2 (fun p o_p ↦ w1 p (M.trans w_o o_p))
    have := Semantic_Substitution_Lemma M w n (at n) ⊤ φ claim
    simp only [Evaluate_and, Evaluate_imp, single_identity] at this
    exact w2 (this.1 (mpp w u_w))

theorem FPT_diamond_helper (φ : Formula) (n : Nat)
  : ⊨ (⊡ (at n ⟷ single n ⊥ (◇ φ))) ↣ (at n ⟷ ◇ φ) := by
  simp only [Formula.isValid, Evaluate_imp, Evaluate_and]
  intro α M u ⟨⟨mp1, mp2⟩, mp3⟩
  constructor
  · intro mp
    have h : □(~φ) = (~(◇ φ)) := by simp
    have h' : (□(~single n ⊥ φ)) = (~◇(single n ⊥ φ)) := by simp
    have h1 := mp1 mp
    have h2 : ¬ Evaluate (M, u) (single n ⊥ (□ (~ φ))) := by rw [h]; simp only [single_neg, ←Evaluate_neg, not_not, h1]
    have ⟨w, u_w, w1, w2⟩ := GL_eval_not_box_prop h2
    simp only [single_neg] at w1
    have claim : Evaluate ⟨M, w⟩ (⊡ (at n ⟷ ⊥)) := by
      simp
      constructor
      · intro con
        have mp3_w := mp3 w u_w
        simp only [Evaluate_and, Evaluate_imp] at mp3_w
        have := mp3_w.1
        simp [con] at this
        simp only [h', ←Evaluate_neg] at w1
        exact w1 this
      · intro o w_o con
        have mp3_o := mp3 o (M.trans u_w w_o)
        simp only [Evaluate_and, Evaluate_imp] at mp3_o
        have := mp3_o.1
        simp [con] at this
        have ⟨p, o_p, p1⟩ := this
        simp only [h', ←Evaluate_neg] at w1
        apply w1 ⟨p, M.trans w_o o_p, p1⟩
    have := Semantic_Substitution_Lemma M w n (at n) ⊥ φ claim
    simp only [Evaluate_and, Evaluate_imp, single_identity] at this
    simp [single_neg, Evaluate_neg] at w2
    exact ⟨w, u_w, this.2 w2⟩
  · intro mpp
    by_contra con
    have claim : Evaluate ⟨M, u⟩ (⊡ (at n ⟷ ⊥)) := by
      simp
      refine ⟨con, fun w u_w con ↦ ?_⟩
      have mp3_w := mp3 w u_w
      simp only [Evaluate_and, Evaluate_imp] at mp3_w
      have ⟨o, w_o, o1⟩ := mp3_w.1 con
      have w1 : Evaluate (M, u) (single n ⊥ (◇φ)) := ⟨o, M.trans u_w w_o, o1⟩
      simp_all
    have := Semantic_Substitution_Lemma M u n (at n) ⊥ (◇ φ) claim
    simp only [Evaluate_and, Evaluate_imp, single_identity] at this
    simp_all

theorem single_imp (n : Nat) (C D E : Formula) : single n C (D ↣ E) = (single n C D) ↣ (single n C E) := by
  simp [single, single_neg]

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

theorem Evaluate_box_dot_iff (φ : Formula) : ⊨ ⊡ (φ ⟷ φ) := by
  simp only [Formula.isValid, Evaluate_and, Evaluate_imp]
  intro α M u
  constructor
  · simp
  · intro w u_w
    simp only [Evaluate_and, Evaluate_imp]
    simp

theorem FPT_box (φ : Formula) (n : Nat) : ⊨ (single n ⊤ (□ φ)) ⟷ (single n (□ single n ⊤ φ) (□ φ)) := by
  intro α M u
  have := FPT_box_helper φ n
  have h := single_preserves_validity n _ (single n ⊤ (□ φ)) this α M u
  simp only [single_imp, Evaluate_imp, single_iff] at h
  have := h (by
    have h : single n (single n ⊤ (□φ)) (⊡ (at n ⟷ single n ⊤ (□ φ))) = (⊡ (((single n ⊤ (□φ)) ⟷ ((single n ⊤ (□ φ)))))) := by
      clear *-
      simp [single]
      constructor
      · apply not_in_single_voc
        apply not_in_single_top_voc
      · apply not_in_single_voc
        simp
        apply not_in_single_top_voc
    rw [h]
    apply Evaluate_box_dot_iff)
  simp_all [single]

theorem FPT_diamond (φ : Formula) (n : Nat) : ⊨ (single n ⊥ (◇ φ)) ⟷ (single n (◇ single n ⊥ φ) (◇ φ)) := by
  intro α M u
  have := FPT_diamond_helper φ n
  have h := single_preserves_validity n _ (single n ⊥ (◇ φ)) this α M u
  simp only [single_imp, Evaluate_imp, single_iff] at h
  have := h (by
    have h : single n (single n ⊥ (◇φ)) (⊡ (at n ⟷ single n ⊥ (◇ φ))) = (⊡ (((single n ⊥ (◇φ)) ⟷ ((single n ⊥ (◇ φ)))))) := by
      clear *-
      simp [single]
      constructor
      · apply not_in_single_voc
        apply not_in_single_bot_voc
      · apply not_in_single_voc
        simp
        apply not_in_single_bot_voc
    rw [h]
    apply Evaluate_box_dot_iff)
  simp_all [single]

-- #axiom_blame FPT_box_helper
-- #axiom_blame FPT_diamond_helper
