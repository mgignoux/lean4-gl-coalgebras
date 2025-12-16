import GL.Logic
import GL.CoalgebraProof
import GL.Game
import GL.CoalgebraGame
import GL.Completeness

def after_box (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inl _, _, R :: _⟩ => R.isBox
  | _ => false

def is_box (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inr R, _, _⟩ => R.isBox
  | _ => false

def non_box_move : coalgebraGame.Pos → coalgebraGame.Pos → Prop :=
  fun x y ↦ move x y ∧ ¬ is_box y

inductive maximal_path (Γ : Sequent) (strat : Strategy coalgebraGame Builder) : Type
| mp : (π : List coalgebraGame.Pos) → (ne : π ≠ []) → (chain : List.IsChain non_box_move π) →
       (max : ¬ ∃ z, non_box_move (π.getLast ne) z) → (head_cases : after_box (π.head ne) ∨ π.head ne = ⟨Sum.inl Γ, [], []⟩)
     → (in_cone : ∀ x ∈ π, inMyCone strat ⟨Sum.inl Γ, [], []⟩ x) → maximal_path Γ strat

@[simp]
def maximal_path.last {Γ : Sequent} {strat : Strategy coalgebraGame Builder} : maximal_path Γ strat → coalgebraGame.Pos
  | .mp π ne _ _ _ _ => π.getLast ne
@[simp]
def maximal_path.first {Γ : Sequent} {strat : Strategy coalgebraGame Builder} : maximal_path Γ strat → coalgebraGame.Pos
  | .mp π ne _ _ _ _ => π.head ne

@[simp]
def maximal_path.under {Γ : Sequent} {strat : Strategy coalgebraGame Builder} : maximal_path Γ strat → List coalgebraGame.Pos
  | .mp π _ _ _ _ _ => π

theorem maximal_path_starts_in_prover_turn {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
  (π : maximal_path Γ strat) :
  coalgebraGame.turn π.first = Prover := by
    match first_def : π.first with
    | ⟨Sum.inl Γ, Γs, Rs⟩ => simp [coalgebraGame]
    | ⟨Sum.inr R, Γs, Rs⟩ =>
      exfalso
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp at first_def
      rcases head_cases with after | root
      · simp [first_def, after_box] at after
      · simp [first_def] at root
        grind

theorem maximal_path_ends_in_prover_turn {Γ : Sequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  (π : maximal_path Γ strat) :
  coalgebraGame.turn π.last = Prover := by
    match last_def : π.last with
    | ⟨Sum.inl Γ, Γs, Rs⟩ => simp [coalgebraGame]
    | ⟨Sum.inr R, Γs, Rs⟩ =>
      exfalso
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      apply max
      have is_winning : winning strat ⟨Sum.inr R, Γs, Rs⟩ := in_cone_winning (by
        simp at last_def
        simp [←last_def]
        apply in_cone
        simp) h
      have B_turn : coalgebraGame.turn ⟨Sum.inr R, Γs, Rs⟩ = Builder := by simp [coalgebraGame]
      have has_moves := winning_has_moves B_turn is_winning
      let z := strat ⟨Sum.inr R, Γs, Rs⟩ B_turn has_moves
      refine ⟨z.1, ?_, ?_⟩
      · apply move_iff_in_moves.2
        simp at last_def
        rw [last_def]
        exact z.2
      · have ⟨z, z_in⟩ := z
        unfold Game.Pos.moves Game.moves at z_in
        simp [coalgebraGame, -SetLike.coe_mem] at z_in
        have ⟨Γ, Γ_R, _, z_eq⟩ := z_in
        subst z_eq
        simp [is_box]

theorem always_exists_maximal_path_from_root (Γ : Sequent) (strat : Strategy coalgebraGame Builder) :
  ∃ π : maximal_path Γ strat, π.first = ⟨Sum.inl Γ, [], []⟩ := by
  sorry

def prover_sequent (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover) := match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => Γ
  | ⟨Sum.inr R, Γ :: Γs, Rs⟩ => False.elim (by simp [coalgebraGame] at h)

def first_sequent {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
  : maximal_path Γ strat → Sequent := fun π ↦
  prover_sequent π.first (maximal_path_starts_in_prover_turn π)

def last_sequent {Γ : Sequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  : maximal_path Γ strat → Sequent := fun π ↦
  prover_sequent π.last (maximal_path_ends_in_prover_turn h π)

def path_relation (Γ : Sequent) (strat : Strategy coalgebraGame Builder) (π₁ π₂ : maximal_path Γ strat)
  := (Relation.Comp move move) π₁.last π₂.first

def gameB_model (Γ : Sequent) {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  : Model (maximal_path Γ strat) where
  V π n := at n ∉ last_sequent h π
  R := Relation.TransGen (path_relation Γ strat) -- maybe two steps of move
  trans := Relation.transitive_transGen
  con_wf := by sorry

theorem move_from_last_implies_box {Γ : Sequent} {strat : Strategy coalgebraGame Builder} (π : maximal_path Γ strat) :
  ∀ x, move π.last x → is_box x := by
  intro x π_x
  by_contra h
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  apply max
  refine ⟨x, ⟨π_x, h⟩⟩

theorem diamond_in_of_move_move_diamond_in {Γ : Sequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  {x z} (hx hz) (x_z : (Relation.Comp move move) x z) : ∀ φ, ◇ φ ∈ prover_sequent x hx → ◇ φ ∈ prover_sequent z hz := by
  simp only [Relation.Comp] at x_z
  have ⟨y, x_y, y_z⟩ := x_z
  rcases x with ⟨Γ | R, Γs, Rs⟩ <;> simp only [coalgebraGame, reduceCtorEq] at hx
  rcases x_y
  case prover R R_Γ =>
  rcases y_z
  case builder Γ' Γ'_R nrep =>
  simp [prover_sequent]
  intro φ φ_in
  simp [Sequent.RuleApps] at R_Γ
  have ⟨ψ, ψ_in, eq⟩ := R_Γ
  cases ψ
  all_goals
    simp at eq
    try subst eq
    try simp [RuleApp.Sequents] at Γ'_R
  case atom =>
    have ⟨nψ_in, eq⟩ := eq
    subst eq
    simp at Γ'_R
  case and =>
    rcases Γ'_R with Γ'_R | Γ'_R
    all_goals
    subst Γ'_R
    simp
    right
    exact φ_in
  case or =>
    subst Γ'_R
    simp
    right
    right
    exact φ_in
  case box =>
    subst Γ'_R
    simp [Sequent.D]
    right
    left
    simp [Formula.isDiamond, φ_in]

theorem diamond_in_last_of_diamond_in_first {Γ : Sequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩) :
∀ π : maximal_path Γ strat, ∀ φ (i : ℕ) (lt : i < π.under.length) helper (ps),
  ◇ φ ∈ prover_sequent ((π.under)[π.under.length - i - 1]'helper) ps → ◇ φ ∈ last_sequent h π := by
  intro π φ i lt helper ps φ_in
  cases i
  case zero =>
    convert φ_in
    simp [last_sequent, List.getLast_eq_getElem]
  case succ i =>
    cases i
    case zero =>
      exfalso
      have P_turn_last := maximal_path_ends_in_prover_turn h π
      have eq : π.under.length - (0 + 1) - 1 = π.under.length - 2 := by omega
      have eq2 : π.under.length - (0 + 1) - 1 + 1 = π.under.length - 1 := by omega
      have eq3 : π.under.length - 1 - 1 = π.under.length - 2 := by omega
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have length_gt_one : π.length > 1 := by
        simp at lt
        grind
      have u₁_last := List.IsChain.getElem chain (π.length - (0 + 1) - 1) (by omega)
      have helper : π[π.length - 1]'(by omega) = π.getLast ne := by grind
      simp_all
      rcases u₁_def : π[π.length - 2] with ⟨Γ | R, Γs, Rs⟩
      · simp_all
        have u₁_last := move_iff_in_moves.1 u₁_last.1
        simp [coalgebraGame] at u₁_last
        have ⟨R, Γ_R, eq⟩ := u₁_last
        rw [←eq] at P_turn_last
        simp [coalgebraGame] at P_turn_last
      · simp at ps
        have helper : ¬ coalgebraGame.turn ⟨Sum.inr R, Γs, Rs⟩ = Prover := by simp [coalgebraGame]
        apply helper
        convert ps
        convert Eq.symm u₁_def
    case succ i =>
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have ne_zero : π.length ≠ 0 := by grind
      have length_gt_two : π.length > 2 := by
        simp at lt
        grind
      have eq3 : π.length - (i + 1 + 1) - 1 = π.length - i - 3 := by omega
      have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by simp_all; omega
      have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
      have u₁_u₂ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
      have P_turn_y : coalgebraGame.turn π[π.length - (i + 1 + 1) - 1] = Prover := by sorry
      have P_turn_u₂ : coalgebraGame.turn π[π.length - (i + 1 + 1) - 1 + 1 + 1] = Prover := by sorry
      have := diamond_in_of_move_move_diamond_in h P_turn_y P_turn_u₂ ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in
      refine diamond_in_last_of_diamond_in_first h (maximal_path.mp π ne chain max head_cases in_cone) φ i (by grind) (by grind) ?_ ?_
      · simp
        convert P_turn_u₂ using 3
        grind
      · convert diamond_in_of_move_move_diamond_in h _ _ ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in using 3
        simp
        · grind
        · exact P_turn_u₂

-- set_option maxHeartbeats 1000000
-- theorem gameB_model_sat {Γ : Sequent} (strat : Strategy coalgebraGame Builder) (π : maximal_path Γ strat)
--   (h : winning strat ⟨Sum.inl Γ, [], []⟩) :
--   ∀ φ ∈ last_sequent h π, ¬ Evaluate ⟨gameB_model Γ h, π⟩ φ := by
--     intro φ φ_in
--     have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
--     rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;> simp only [last_def, coalgebraGame, reduceCtorEq] at P_turn_y
--     have eq : Γ' = last_sequent h π := by
--       unfold last_sequent
--       simp only [last_def]
--       simp [prover_sequent]
--     subst eq
--     have in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ π.last := by
--       rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
--       apply in_cone
--       simp
--     cases φ
--     case bottom => simp_all
--     case top => -- if its top then builder cannot have a winning strategy
--       let next_move : gamePos := ⟨Sum.inr (RuleApp.top (last_sequent h π) φ_in), (last_sequent h π) :: Γs', Rs'⟩
--       have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
--       have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
--         simp only [last_def]
--         unfold next_move
--         simp [coalgebraGame, Sequent.RuleApps]
--         refine ⟨⊤, φ_in, by simp⟩
--       have still_winning_next : winning strat next_move :=
--         in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
--       have has_moves := winning_has_moves B_turn_next still_winning_next
--       unfold Game.moves next_move at has_moves
--       simp [coalgebraGame, RuleApp.Sequents] at has_moves
--     case atom n =>
--       simp [gameB_model, φ_in]
--     case neg_atom n =>
--       simp [gameB_model]
--       intro nφ_in
--       let next_move : gamePos := ⟨Sum.inr (RuleApp.ax (last_sequent h π) n ⟨nφ_in, φ_in⟩), (last_sequent h π) :: Γs', Rs'⟩
--       have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
--       have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
--         simp only [last_def]
--         unfold next_move
--         simp [coalgebraGame, Sequent.RuleApps]
--         refine ⟨at n, nφ_in, by simp; exact φ_in⟩
--       have still_winning_next : winning strat next_move :=
--         in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
--       have has_moves := winning_has_moves B_turn_next still_winning_next
--       unfold Game.moves next_move at has_moves
--       simp [coalgebraGame, RuleApp.Sequents] at has_moves
--     case or φ1 φ2 => -- then we will make a move
--       let next_move : gamePos := ⟨Sum.inr (RuleApp.or (last_sequent h π) φ1 φ2 φ_in), (last_sequent h π) :: Γs', Rs'⟩
--       have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
--       have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
--         simp only [last_def]
--         unfold next_move
--         simp [coalgebraGame, Sequent.RuleApps]
--         refine ⟨φ1 v φ2, φ_in, by simp⟩
--       exfalso
--       rcases π with ⟨π, ne, chain, max⟩
--       apply max
--       refine ⟨next_move, ?_, ?_⟩
--       · exact move_iff_in_moves.2 next_in_moves
--       · unfold next_move
--         simp [is_box, RuleApp.isBox]
--     case and φ1 φ2  => -- then we will make a move
--       let next_move : gamePos := ⟨Sum.inr (RuleApp.and (last_sequent h π) φ1 φ2 φ_in), (last_sequent h π) :: Γs', Rs'⟩
--       have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
--       have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
--         simp only [last_def]
--         unfold next_move
--         simp [coalgebraGame, Sequent.RuleApps]
--         refine ⟨φ1 & φ2, φ_in, by simp⟩
--       exfalso
--       rcases π with ⟨π, ne, chain, max⟩
--       apply max
--       refine ⟨next_move, ?_, ?_⟩
--       · exact move_iff_in_moves.2 next_in_moves
--       · unfold next_move
--         simp [is_box, RuleApp.isBox]
--     case diamond φ =>
--       simp
--       intro ρ π_ρ
--       have φ_in : ◇ φ ∈ last_sequent h ρ := by
--         simp [gameB_model] at π_ρ
--         cases π_ρ
--         case single π_ρ =>
--           simp only [path_relation] at π_ρ
--           have in_first := diamond_in_of_move_move_diamond_in h (maximal_path_ends_in_prover_turn h π) (maximal_path_starts_in_prover_turn ρ) π_ρ φ φ_in
--           apply diamond_in_last_of_diamond_in_first h ρ φ (ρ.under.length - 1)
--           · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
--             simp
--             grind
--           · convert in_first
--             simp
--             grind
--           · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
--             simp
--             grind
--           · convert maximal_path_starts_in_prover_turn ρ
--             simp
--             grind
--       have := gameB_model_sat strat ρ h (◇ φ) φ_in -- formula gets smaller
--       simp at this
--     case box φ =>
--       simp
--       sorry

def gameB_general_helper {Δ : Sequent} (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Δ, [], []⟩) :
∀ π : maximal_path Δ strat, ∀ φ (i : ℕ) (lt : i < π.under.length) helper (ps),
  φ ∈ prover_sequent ((π.under)[π.under.length - i - 1]'helper) ps → ¬Evaluate (gameB_model Δ h, π) φ := by
  intro π φ i lt helper ps φ_in
  cases i
  case zero =>
    have is_last : π.under[π.under.length - 0 - 1] = π.last := by sorry
    simp_all only
    have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
    rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;> simp only [last_def, coalgebraGame, reduceCtorEq] at P_turn_y
    have eq : Γ' = last_sequent h π := by
      unfold last_sequent
      simp only [last_def]
      simp [prover_sequent]
    subst eq
    have in_cone : inMyCone strat ⟨Sum.inl Δ, [], []⟩ π.last := by
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      apply in_cone
      simp
    cases φ
    case bottom => simp_all
    case top =>
      let next_move : gamePos := ⟨Sum.inr (RuleApp.top (last_sequent h π) φ_in), (last_sequent h π) :: Γs', Rs'⟩
      have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
      have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
        simp only [last_def]
        unfold next_move
        simp [coalgebraGame, Sequent.RuleApps]
        refine ⟨⊤, φ_in, by simp⟩
      have still_winning_next : winning strat next_move :=
        in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
      have has_moves := winning_has_moves B_turn_next still_winning_next
      unfold Game.moves next_move at has_moves
      simp [coalgebraGame, RuleApp.Sequents] at has_moves
    case atom n =>
      simp [gameB_model]
      exact φ_in
    case neg_atom n =>
      simp [gameB_model]
      intro nφ_in
      let next_move : gamePos := ⟨Sum.inr (RuleApp.ax (last_sequent h π) n ⟨nφ_in, φ_in⟩), (last_sequent h π) :: Γs', Rs'⟩
      have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
      have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
        simp only [last_def]
        unfold next_move
        simp [coalgebraGame, Sequent.RuleApps]
        refine ⟨at n, nφ_in, by simp; exact φ_in⟩
      have still_winning_next : winning strat next_move :=
        in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
      have has_moves := winning_has_moves B_turn_next still_winning_next
      unfold Game.moves next_move at has_moves
      simp [coalgebraGame, RuleApp.Sequents] at has_moves
    case or φ1 φ2 => -- then we will make a move
      let next_move : gamePos := ⟨Sum.inr (RuleApp.or (last_sequent h π) φ1 φ2 φ_in), (last_sequent h π) :: Γs', Rs'⟩
      have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
      have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
        simp only [last_def]
        unfold next_move
        simp [coalgebraGame, Sequent.RuleApps]
        refine ⟨φ1 v φ2, φ_in, by simp⟩
      exfalso
      rcases π with ⟨π, ne, chain, max⟩
      apply max
      refine ⟨next_move, ?_, ?_⟩
      · exact move_iff_in_moves.2 next_in_moves
      · unfold next_move
        simp [is_box, RuleApp.isBox]
    case and φ1 φ2  => -- then we will make a move
      let next_move : gamePos := ⟨Sum.inr (RuleApp.and (last_sequent h π) φ1 φ2 φ_in), (last_sequent h π) :: Γs', Rs'⟩
      have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
      have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
        simp only [last_def]
        unfold next_move
        simp [coalgebraGame, Sequent.RuleApps]
        refine ⟨φ1 & φ2, φ_in, by simp⟩
      exfalso
      rcases π with ⟨π, ne, chain, max⟩
      apply max
      refine ⟨next_move, ?_, ?_⟩
      · exact move_iff_in_moves.2 next_in_moves
      · unfold next_move
        simp [is_box, RuleApp.isBox]
    case diamond φ =>
      simp
      intro ρ π_ρ
      apply gameB_general_helper strat h ρ φ (ρ.under.length - 1)
      · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
        simp
        grind
      · have φ_in_2 : φ ∈ first_sequent ρ := by
          sorry
        convert φ_in_2
        simp [first_sequent]
        grind
      · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
        simp
        grind
      · convert (maximal_path_starts_in_prover_turn ρ)
        rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
        simp
        grind
    case box φ =>
      simp
      sorry
  case succ i =>
    cases i
    case zero =>
      exfalso
      have P_turn_last := maximal_path_ends_in_prover_turn h π
      have eq : π.under.length - (0 + 1) - 1 = π.under.length - 2 := by omega
      have eq2 : π.under.length - (0 + 1) - 1 + 1 = π.under.length - 1 := by omega
      have eq3 : π.under.length - 1 - 1 = π.under.length - 2 := by omega
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have length_gt_one : π.length > 1 := by
        simp at lt
        grind
      have u₁_last := List.IsChain.getElem chain (π.length - (0 + 1) - 1) (by omega)
      have helper : π[π.length - 1]'(by omega) = π.getLast ne := by grind
      simp_all
      rcases u₁_def : π[π.length - 2] with ⟨Γ | R, Γs, Rs⟩
      · simp_all
        have u₁_last := move_iff_in_moves.1 u₁_last.1
        simp [coalgebraGame] at u₁_last
        have ⟨R, Γ_R, eq⟩ := u₁_last
        rw [←eq] at P_turn_last
        simp [coalgebraGame] at P_turn_last
      · simp at ps
        have helper : ¬ coalgebraGame.turn ⟨Sum.inr R, Γs, Rs⟩ = Prover := by simp [coalgebraGame]
        apply helper
        convert ps
        convert Eq.symm u₁_def
    case succ i =>
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have ne_zero : π.length ≠ 0 := by grind
      have length_gt_two : π.length > 2 := by
        simp at lt
        grind
      have eq3 : π.length - (i + 1 + 1) - 1 = π.length - i - 3 := by omega
      have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by simp_all; omega
      have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
      have u₁_u₂ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
      have no_box_u₁ := y_u₁.2
      simp at no_box_u₁
      simp at φ_in
      rcases y_def : π[π.length - (i + 1 + 1) - 1] with ⟨Γ | R, Γs, Rs⟩ <;> simp [y_def] at ps <;> simp [coalgebraGame] at ps
      simp [y_def] at φ_in
      simp [y_def] at y_u₁
      have y_u₁ := move_iff_in_moves.1 y_u₁.1
      simp [Game.moves, coalgebraGame] at y_u₁
      have ⟨R, R_Γ, u₁_def⟩ := y_u₁
      have u₁_u₂ : non_box_move (Sum.inr R, Γ :: Γs, Rs) (π[π.length - (i + 1 + 1) - 1 + 1 + 1]'(by grind)) := by
        convert u₁_u₂ -- dont understand why simp or rw doesn't do this
      have u₁_u₂ := move_iff_in_moves.1 u₁_u₂.1
      simp [Game.moves, coalgebraGame] at u₁_u₂
      have ⟨Γ', Γ'_R, no_rep, u₂_def⟩ := u₁_u₂
      have P_turn_u₂ : coalgebraGame.turn (Sum.inl Γ', Γ :: Γs, R :: Rs) = Prover := by simp [coalgebraGame]
      have eq : π.length - i - 1 = π.length - (i + 1 + 1) - 1 + 1 + 1 := by
        simp_all
        omega
      have ih := fun φ ↦ gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) φ i (by grind) (by grind) (by
        simp_all
        convert P_turn_u₂
        simp [u₂_def]
        simp_all
        rfl)
      simp at ih
      simp [←eq] at u₂_def
      have ih_imp : ∀ φ ∈ Γ', ¬Evaluate (gameB_model Δ h, maximal_path.mp π ne chain max head_cases in_cone) φ := by
        convert ih
        have h : Γ' = prover_sequent (Sum.inl Γ', Γ :: Γs, R :: Rs) (by simp [coalgebraGame]) := by simp [prover_sequent]
        convert h
        convert Eq.symm u₂_def using 2
      by_cases φ ∈ Γ'
      case pos φ_in =>
        apply ih_imp φ
        exact φ_in
      case neg nφ_in =>
        cases R <;> simp [RuleApp.Sequents] at Γ'_R
        case and Δ ψ₁ ψ₂ in_Δ _ _ _ =>
          have ⟨eq1, eq2⟩ : φ = (ψ₁ & ψ₂) ∧ Γ = Δ := by
            rcases Γ'_R with eq | eq <;> subst eq
            all_goals
            simp [Sequent.RuleApps] at R_Γ
            have ⟨χ, χ_in, eq⟩ := R_Γ
            cases χ <;> simp at eq
            simp [eq]
            by_contra ne
            apply nφ_in
            simp
            refine Or.inr ⟨?_, ne⟩
            convert φ_in
            simp [prover_sequent, eq]
          subst_eqs
          simp only [Evaluate, not_and_or]
          rcases Γ'_R with eq | eq <;> subst eq
          · left
            apply ih_imp ψ₁; simp
          · right
            apply ih_imp ψ₂; simp
        case or Δ ψ₁ ψ₂ in_Δ _ _ _ =>
          have ⟨eq1, eq2⟩ : φ = (ψ₁ v ψ₂) ∧ Γ = Δ := by
            subst Γ'_R
            simp [Sequent.RuleApps] at R_Γ
            have ⟨χ, χ_in, eq⟩ := R_Γ
            cases χ <;> simp at eq
            simp [eq]
            by_contra ne
            apply nφ_in
            simp
            refine Or.inr (Or.inr ⟨?_, ne⟩)
            convert φ_in
            simp [prover_sequent, eq]
          subst_eqs
          simp
          constructor
          · apply ih_imp ψ₁; simp
          · apply ih_imp ψ₂; simp
        case box Δ ψ ψ_in _ _ _ => -- if this breaks in the future, then if u₁ is a box then we have a contradiction since u₁ sees u₂
          exfalso
          apply no_box_u₁
          have h : is_box ⟨Sum.inr (RuleApp.box Δ ψ ψ_in), Γ :: Γs, Rs⟩ := by simp [is_box, RuleApp.isBox]
          convert h
          exact Eq.symm u₁_def

theorem gameB_general {Γ : Sequent}
  (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  : ¬ ⊨ Γ := by
    simp [Sequent.isValid]
    use maximal_path Γ strat
    use gameB_model Γ h
    have ⟨π, π_head_eq⟩ := always_exists_maximal_path_from_root Γ strat
    use π
    intro φ φ_in
    apply gameB_general_helper strat h π φ (π.under.length - 1) ?_ ?_ ?_ ?_
    · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have h : (π[π.length - (π.length - 1) - 1]'(by grind)) = π.head ne := by
        grind
      simp [h]
      simp at π_head_eq
      simp [π_head_eq, coalgebraGame]
    · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have h : (π[π.length - (π.length - 1) - 1]'(by grind)) = π.head ne := by
        grind
      simp [h]
      simp at π_head_eq
      simp [π_head_eq]
      simp [prover_sequent, φ_in]

def startPos (Γ : Sequent) : gamePos := ⟨Sum.inl Γ, [], []⟩

theorem Soundness_seq (Γ : Sequent) : ⊨ Γ → ⊢ Γ := by
  intro Γ_sat
  rcases gamedet coalgebraGame (startPos Γ) with builder_wins | prover_wins
  · have ⟨strat, h⟩ := builder_wins
    have nΓ_sat := gameB_general strat h
    exfalso
    exact nΓ_sat Γ_sat
  · have ⟨strat, h⟩ := prover_wins
    exact gameP_general strat h

theorem Soundness (φ : Formula) : ⊨ φ → ⊢ φ := by
  intro φ_val
  apply Soundness_seq {φ}
  simp_all [Formula.isValid, Sequent.isValid]
