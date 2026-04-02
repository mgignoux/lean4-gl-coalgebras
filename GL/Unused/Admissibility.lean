import GL.Syntax
import GL.CoalgebraProof

/- ADMISSIBILITY -/
-- This section aims to show admissibility of the weakening rule as well stating that there exists a proof of
-- ~φ,φ for any formula φ. This should all be possible but it is not a part of my thesis work and I probably will
-- not work any more on this unless I have the time. The leftover sorrys are a lot of tedious facts about Finset.

theorem and_subproofs_left (𝕏 : Proof) (x : 𝕏.X) (A B : Formula) (Δ : Sequent) (AB_in : (A & B) ∈ Δ)(h : r 𝕏.α x = RuleApp.and Δ A B AB_in) : 𝕏 ⊢ Δ \ {A & B} ∪ {A} := by
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

theorem and_subproofs_right (𝕏 : Proof) (x : 𝕏.X) (A B : Formula) (Δ : Sequent) (AB_in : (A & B) ∈ Δ)(h : r 𝕏.α x = RuleApp.and Δ A B AB_in) : 𝕏 ⊢ Δ \ {A & B} ∪ {B} := by
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

theorem box_subproof (𝕏 : Proof) (x : 𝕏.X) (A : Formula) (Δ : Sequent) (A_in : □ A ∈ Δ) (h : r 𝕏.α x = RuleApp.box Δ A A_in) : 𝕏 ⊢ (Δ \ {□ A}).D ∪ {A} := by
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

theorem weakening_helper {Γ : Sequent} {A B D : Formula} (A_ne : D ≠ A) :  Γ \ {D} ∪ {B} ∪ {A} = (Γ ∪ {A}) \ {D} ∪ {B} := by
  aesop

lemma Sequent.D_size_wod_leq_size_wod (Γ : Sequent) : (D Γ).size_without_diamond ≤ Γ.size_without_diamond := by
  induction Γ using Finset.induction
  case empty => simp [Sequent.D]
  case insert A Δ A_ni ih =>
    have dis : Disjoint {A} Δ := Finset.disjoint_singleton_left.2 A_ni
    simp only [Finset.insert_eq, size_wod_disjoint dis]
    sorry -- very doable just annoying

theorem weakening (A : Formula) (Δ : Sequent) : (∃ 𝕏, 𝕏 ⊢ Δ) → (∃ 𝕏, 𝕏 ⊢ Δ ∪ {A}) := by
  intro ⟨𝕏, x, x_Δ⟩
  by_cases A ∈ Δ
  case pos A_in => refine ⟨𝕏, x, by simp [x_Δ, A_in]⟩
  case neg A_ni =>
    cases rule : r 𝕏.α x
    case top Γ top_in =>
      use {
        X := Unit
        α y := ⟨RuleApp.top (Γ ∪ {A}) (by simp_all) , {}⟩--by simp_all only [f, Finset.mem_union]; left; subst x_Δ; exact top_in), {}⟩ -- : RuleApp × Sequent × Multiset X
        h := by aesop}
      use ()
      simp [f, r]
      aesop
    case ax Γ n lem_in =>
      use {
        X := Unit
        α y := ⟨RuleApp.ax (Γ ∪ {A}) n (by simp_all) , {}⟩--by simp_all only [f, Finset.mem_union]; left; subst x_Δ; exact top_in), {}⟩ -- : RuleApp × Sequent × Multiset X
        h := by aesop}
      use ()
      simp [f, r]
      aesop
    case and Γ B C and_in =>
      simp only [f, rule] at x_Δ
      subst x_Δ
      have for_term1 : Sequent.size_without_diamond ((fₙ (r 𝕏.α x)) ∪ {B}) < Sequent.size_without_diamond Γ := by
        sorry
      have for_term2 : Sequent.size_without_diamond ((fₙ (r 𝕏.α x)) ∪ {C}) < Sequent.size_without_diamond Γ := by
        sorry
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
            simp only [p, List.map, List.cons_eq_cons, T, pfl, pfr]
            cases r_defl : (𝕐l.α yl).1 <;> cases r_defr : (𝕐r.α yr).1 <;> simp only [fₙ_alternate]
            all_goals
              constructor
              all_goals
                sorry }
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
          have ⟨𝕐, y, pf⟩ := weakening B ((fₙ (r 𝕏.α x)).D ∪ {C, ◇ B}) (by
            have for_termination : Sequent.size_without_diamond ((fₙ (r 𝕏.α x)).D ∪ {C}) < Sequent.size_without_diamond (f (r 𝕏.α x)) := by
              calc
                _ ≤ Sequent.size_without_diamond ((fₙ (r 𝕏.α x)) ∪ {C}) := by
                  have := Sequent.D_size_wod_leq_size_wod (fₙ (r 𝕏.α x))
                  sorry

                _ < Sequent.size_without_diamond (f (r 𝕏.α x)) := by
                  simp [rule, f, fₙ_alternate]
                  sorry
            have ⟨𝕐, y, pf⟩ := weakening (◇ B) ((fₙ (r 𝕏.α x)).D ∪ {C}) (by use 𝕏; convert (box_subproof 𝕏 x C Γ box_in rule); simp [fₙ, rule, f, fₚ]) -- put in seperate theorem
            clear for_termination
            refine ⟨𝕐, y, ?_⟩
            · have h : ({C} : Sequent) ∪ {◇ B} = {C, ◇ B} := by aesop
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
                simp [Sequent.D]
                sorry }
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
                simp only [Sequent.D, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filterMap]
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

lemma helper2 {A B : Formula} : {A, ~A} ∪ {~B} = {A&B, ~A, ~B} \ {A&B} ∪ ({A} : Sequent) := by sorry

theorem extended_lem (A : Formula) : ∃ (𝕏 : Proof), 𝕏 ⊢ {A, ~A} := by
  induction A <;> simp only [Formula.neg]
  case bottom =>
    use {
      X := Unit
      α x := ⟨RuleApp.top {⊥,⊤} (by simp), {}⟩ -- : RuleApp × Sequent × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
    rfl
  case top =>
    use {
      X := Unit
      α x := ⟨RuleApp.top {⊤,⊥} (by simp), {}⟩ -- : RuleApp × Sequent × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
    rfl
  case atom n =>
    use {
      X := Unit
      α x := ⟨RuleApp.ax {at n, na n} n (by simp), {}⟩ -- : RuleApp × Sequent × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
  case neg_atom n =>
    use {
      X := Unit
      α x := ⟨RuleApp.ax {na n, at n} n (by simp), {}⟩ -- : RuleApp × Sequent × Multiset X
      h := by aesop}
    use ()
    simp [r, f]
  case and A B ihA ihB =>
    have ⟨𝕏, x, x_A⟩ := weakening (~B) {A,~A} ihA
    have ⟨𝕐, y, y_B⟩ := weakening (~A) {B,~B} ihB
    let X := 𝕏.X ⊕ 𝕐.X ⊕ Bool -- prob need like 2 things here
    let α : X → T.obj X  -- : RuleApp × Sequent × Multiset X
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
    let α : X → T.obj X  -- : RuleApp × Sequent × Multiset X
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
