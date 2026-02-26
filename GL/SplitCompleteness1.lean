import GL.Logic
import GL.Semantics
import GL.SplitCoalgebraProof
import GL.AxiomBlame
import GL.Game
import GL.SplitCoalgebraGame

namespace Split

def rewind_history_one_step
  (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨ coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅) -- (h : winning strat ⟨Sum.inl Γ, [], []⟩)  (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  : coalgebraGame.Pos :=
  match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => ⟨Sum.inr (Rs.head (by simp_all [coalgebraGame])), Γs, Rs.tail⟩
  | ⟨Sum.inr R, Γs, Rs⟩ => ⟨Sum.inl (Γs.head (by simp_all [coalgebraGame])), Γs.tail, Rs⟩

theorem rewind_history_one_step_in_cone {Γ} (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨ coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅) -- (h : winning strat ⟨Sum.inl Γ, [], []⟩)  (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  (strat : Strategy coalgebraGame Prover) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  : inMyCone strat ⟨Sum.inl Γ, [], []⟩ (rewind_history_one_step g h) := by
  cases in_cone <;> simp at h
  case myStep q q_in_cone q_has_moves P_turn_q =>
    convert q_in_cone
    have := (strat q P_turn_q q_has_moves).2
    rcases q with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at P_turn_q
    unfold Game.Pos.moves Game.moves at this
    simp [coalgebraGame, -SetLike.coe_mem] at this
    have ⟨R, R_Γ, strat_def⟩ := this
    simp [←strat_def]
    simp [rewind_history_one_step]
  case oStep q q_in_cone B_turn_q g_in_moves_q =>
    convert q_in_cone
    rcases q with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at B_turn_q
    unfold Game.moves at g_in_moves_q
    simp [coalgebraGame, -SetLike.coe_mem] at g_in_moves_q
    have ⟨R, R_Γ, _, g_def⟩ := g_in_moves_q
    simp [←g_def]
    simp [rewind_history_one_step]

def rewind_history
  (g : coalgebraGame.Pos)
  (n : Fin ((if coalgebraGame.turn g = Prover then min (2 * g.2.1.length + 1) (2 * g.2.2.length) else min (2 * g.2.1.length) (2 * g.2.2.length + 1)) + 1) )
  : coalgebraGame.Pos :=
  match n_def : n.1 with
    | 0 => g
    | m + 1 => rewind_history (rewind_history_one_step g (by
      have ⟨n_val, n_prop⟩ := n
      simp_all
      rcases g with ⟨Γ | R, Γs, Rs⟩ <;> simp_all [coalgebraGame] <;> grind)) ⟨m, by
      have ⟨n_val, n_prop⟩ := n
      simp_all
      rcases g with ⟨Γ | R, Γs, Rs⟩ <;> simp_all [coalgebraGame, rewind_history_one_step]
      · simp [coalgebraGame] at n_prop
        grind
      · simp [coalgebraGame] at n_prop
        grind⟩

theorem rewind_history_in_cone {Γ} (g : coalgebraGame.Pos) (n : Fin ((if coalgebraGame.turn g = Prover then min (2 * g.2.1.length + 1) (2 * g.2.2.length) else min (2 * g.2.1.length) (2 * g.2.2.length + 1)) + 1) )
  (strat : Strategy coalgebraGame Prover) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  : inMyCone strat ⟨Sum.inl Γ, [], []⟩ (rewind_history g n) := by
  unfold rewind_history
  split
  · exact in_cone
  · apply rewind_history_in_cone
    apply rewind_history_one_step_in_cone
    exact in_cone

@[simp]
lemma rewind_history_zero (g : coalgebraGame.Pos) : rewind_history g 0 = g := by
  simp [rewind_history]

def btype (Γ : SplitSequent) (strat : Strategy coalgebraGame Prover) :=
 {g // inMyCone strat ⟨Sum.inl Γ, [], []⟩ g ∧ coalgebraGame.turn g = Builder}

def builder_RuleApp (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Builder) : RuleApp := match g with
  | ⟨Sum.inr R, _, _⟩ => R
  | ⟨Sum.inl _, _, _⟩ => False.elim (by simp_all [coalgebraGame])

theorem in_cone_winning {G : Game} {i : Player} {g g' : G.Pos} {strat : Strategy G i}
  (in_cone : inMyCone strat g g') (h : winning strat g) : winning strat g' := by
  induction in_cone
  case nil => exact h
  case myStep q q_in_cone has_moves my_turn ih =>
    apply winning_of_winning_move
    exact ih
  case oStep q q' q_in_cone o_turn in_moves ih =>
    exact @winning_of_whatever_other_move G i strat q o_turn ih ⟨q', in_moves⟩

/- Defining next move without a repeat -/
def next_next {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (nrep : Δ ∉ g.1.2.1) (pos : Δ ∈ (builder_RuleApp g.1 g.2.2).SplitSequents) : btype Γ strat :=
  let next : gamePos := ⟨Sum.inl $ Δ, g.1.2.1, builder_RuleApp g.1 g.2.2 :: g.1.2.2⟩
  have P_next : coalgebraGame.turn next = Prover := by unfold Game.turn next; simp [coalgebraGame]
  have next_in_moves : next ∈ coalgebraGame.moves g.1 := by
    rcases g with ⟨⟨Γ | R, Γs, Rs⟩, _, b_move⟩ <;> simp [coalgebraGame] at b_move
    unfold next
    simp at nrep
    simp [builder_RuleApp] at pos
    simp [coalgebraGame, nrep, pos, builder_RuleApp]
  have still_winning_next : winning strat next := by
    have g_winning := in_cone_winning g.2.1 h
    exact @winning_of_whatever_other_move coalgebraGame Prover strat g.1 g.2.2 g_winning ⟨next, next_in_moves⟩
  have P_has_moves_next : (coalgebraGame.moves next).Nonempty := winning_has_moves P_next still_winning_next
  let next_next := strat next P_next P_has_moves_next
  have B_next_next : coalgebraGame.turn next_next.1 = Builder := by
    rcases next_next with ⟨⟨Γ | R, Γs, Rs⟩, in_moves⟩
    · unfold Game.Pos.moves Game.moves at in_moves
      simp [coalgebraGame] at in_moves
      rcases next with ⟨Γ | R, Γs, Rs⟩
      · simp at in_moves
      · simp [coalgebraGame] at P_next
    · unfold Game.Pos.moves Game.moves
      simp [coalgebraGame]
  have next_next_in_cone : inMyCone strat (Sum.inl Γ, [], []) next_next := by
    have := @inMyCone.oStep _ _ strat _ _ _ g.2.1 g.2.2 next_in_moves
    exact inMyCone.myStep this P_has_moves_next P_next
  -- have rewind_next_next_in_cone : rewind_in_cone Γ next_next strat := by
  --   have := rewind_in_cone_of_step Γ g.1 strat g.2.1 next (move_iff_in_moves.2 next_in_moves) (@inMyCone.oStep _ _ strat _ _ _ g_in_cone g.2.2 next_in_moves)
  --   exact rewind_in_cone_of_step Γ next strat this next_next (move_iff_in_moves.2 next_next.2) next_next_in_cone
  ⟨next_next, next_next_in_cone, B_next_next⟩

theorem next_next_cor {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (nrep : Δ ∉ g.1.2.1) (pos : Δ ∈ (builder_RuleApp g.1 g.2.2).SplitSequents) :
  f (builder_RuleApp (next_next g h nrep pos).1 (next_next g h nrep pos).2.2) = Δ := by
  -- have g_in_cone := in_cone_of_rewind_in_cone Γ g.1 strat g.2.1
  let next : gamePos := ⟨Sum.inl $ Δ, g.1.2.1, builder_RuleApp g.1 g.2.2 :: g.1.2.2⟩
  have P_next : coalgebraGame.turn next = Prover := by unfold Game.turn next; simp [coalgebraGame]
  have next_in_moves : next ∈ coalgebraGame.moves g.1 := by
    rcases g with ⟨⟨Γ | R, Γs, Rs⟩, _, b_move⟩ <;> simp [coalgebraGame] at b_move
    unfold next
    simp at nrep
    simp [builder_RuleApp] at pos
    simp [coalgebraGame, nrep, pos, builder_RuleApp]
  have still_winning_next : winning strat next := by
    have g_winning := in_cone_winning g.2.1 h
    exact @winning_of_whatever_other_move coalgebraGame Prover strat g.1 g.2.2 g_winning ⟨next, next_in_moves⟩
  have P_has_moves_next : (coalgebraGame.moves next).Nonempty := winning_has_moves P_next still_winning_next
  let next_next' := strat next P_next P_has_moves_next
  have B_next_next : coalgebraGame.turn next_next'.1 = Builder := by
    rcases next_next' with ⟨⟨Γ | R, Γs, Rs⟩, in_moves⟩
    · unfold Game.Pos.moves Game.moves at in_moves
      simp [coalgebraGame] at in_moves
      rcases next with ⟨Γ | R, Γs, Rs⟩
      · simp at in_moves
      · simp [coalgebraGame] at P_next
    · unfold Game.Pos.moves Game.moves
      simp [coalgebraGame]
  have next_next_in_cone : inMyCone strat (Sum.inl Γ, [], []) next_next' := by
    have := @inMyCone.oStep _ _ strat _ _ _ g.2.1 g.2.2 next_in_moves
    exact inMyCone.myStep this P_has_moves_next P_next
  have h : next_next'.1 = (next_next g h nrep pos).1 := by grind [next_next]
  simp [←h]
  have next_next_in_moves := next_next'.2
  unfold next Game.Pos.moves Game.moves coalgebraGame at next_next_in_moves
  simp only [Finset.mem_map] at next_next_in_moves
  have ⟨R, R_prop, R_eq⟩ := next_next_in_moves
  simp at R_eq
  simp [←R_eq]
  simp [builder_RuleApp]
  simp [SplitSequent.RuleApps] at R_prop
  rcases R_prop with R_prop | R_prop
  all_goals
    have ⟨φ, φ_in, φ_prop⟩ := R_prop
    cases φ <;> simp at φ_prop <;> try grind [f]

theorem history_length_in_cone {Γ : SplitSequent} (strat : Strategy coalgebraGame Prover) (g : coalgebraGame.Pos)
(in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g) :
  (coalgebraGame.turn g = Prover → g.2.1.length = g.2.2.length) ∧ (coalgebraGame.turn g = Builder → g.2.1.length = g.2.2.length + 1) := by
  induction in_cone
  case nil => simp [coalgebraGame]
  case myStep q q_in_cone q_has_moves p_turn_q ih =>
    rcases next_def : (strat q p_turn_q q_has_moves) with ⟨⟨Γ | R, Γs, Rs⟩, in_moves⟩ <;> rcases q with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at p_turn_q
    · unfold Game.Pos.moves at in_moves
      simp [coalgebraGame] at in_moves
    · unfold Game.Pos.moves at in_moves
      simp [coalgebraGame] at in_moves
      simp_all [coalgebraGame]
      grind
  case oStep q r q_in_cone b_turn_q in_moves ih =>
    rcases q_def : q with ⟨Γ | R, Γs, Rs⟩ <;> simp [q_def, coalgebraGame] at b_turn_q
    rcases r_def : r with ⟨Γ | R, Γs, Rs⟩
    · unfold Game.moves at in_moves
      simp [coalgebraGame, q_def, r_def] at in_moves
      subst_eqs
      simp_all [coalgebraGame]
      grind
    · unfold Game.moves at in_moves
      simp [coalgebraGame, q_def, r_def] at in_moves

/- Defining next move with a repeat-/
noncomputable
def rep_pos {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
 (rep : Δ ∈ g.1.2.1) : coalgebraGame.Pos :=
  let n := (List.mem_iff_get.1 rep).choose
  rewind_history g.1 ⟨2 * n.1, by
    have := (history_length_in_cone strat g.1 g.2.1).2 g.2.2
    unfold instMinNat min minOfLe
    simp [g.2.2]
    split <;> try grind⟩

lemma rewind_turn_one_step  {g n h1 h2} : coalgebraGame.turn (rewind_history g ⟨n + 1, h1⟩) = other (coalgebraGame.turn (rewind_history g ⟨n, h2⟩)) := by
  cases n
  case zero =>
    rcases g with ⟨Γ | R, Γs, Rs⟩ <;> simp [rewind_history, rewind_history_one_step, coalgebraGame]
  case succ n =>
    unfold rewind_history
    exact @rewind_turn_one_step (rewind_history_one_step g _) n _ _

-- Ask Malvin why this keeps happening?????

theorem rewind_turn {g n} : if Even n.1 then coalgebraGame.turn (rewind_history g n) = coalgebraGame.turn g
   else coalgebraGame.turn (rewind_history g n) = other (coalgebraGame.turn g) := by
  induction n using Fin.induction
  case zero => simp
  case succ k ih =>
    have ⟨k_val, k_prop⟩ := k
    simp_all
    by_cases Even k_val
    · have h : ¬ Even (k_val + 1) := by grind
      simp_all only [↓reduceIte]
      simp only [←ih]
      exact rewind_turn_one_step
    · have h : Even (k_val + 1) := by grind
      simp_all only [↓reduceIte]
      have ih := congrArg other ih
      simp at ih
      simp only [←ih]
      exact rewind_turn_one_step

theorem rewind_history_one_step_correspondence {Γ g} (strat : Strategy coalgebraGame Prover)
  {h0 h1 h2}  (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  : f (builder_RuleApp (rewind_history_one_step g h0) h1) = g.2.1[0]'h2 := by
  cases in_cone <;> try simp at h2
  case myStep q q_in_cone q_has_moves P_turn_q =>
    have := (strat q P_turn_q q_has_moves).2
    rcases q with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at P_turn_q
    unfold Game.Pos.moves Game.moves at this
    simp [coalgebraGame, -SetLike.coe_mem] at this
    have ⟨R, R_Γ, strat_def⟩ := this
    simp [←strat_def] at *
    simp [rewind_history_one_step]
    grind
  case oStep q q_in_cone B_turn_q g_in_moves_q =>
    cases q_in_cone <;> simp [coalgebraGame] at B_turn_q
    case myStep q' q_in_cone' q_has_moves' P_turn_q' =>
      have := (strat q' P_turn_q' q_has_moves').2
      simp [coalgebraGame, -SetLike.coe_mem] at this
      rcases q' with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at P_turn_q'
      unfold Game.Pos.moves Game.moves at this
      simp [-SetLike.coe_mem] at this
      have ⟨R, R_Γ, strat_def⟩ := this
      simp [←strat_def] at *
      simp [coalgebraGame, -SetLike.coe_mem] at g_in_moves_q
      simp_all
      have ⟨Δ, Δ_R, _, g_def⟩ := g_in_moves_q
      subst g_def
      simp [rewind_history_one_step, builder_RuleApp]
      simp [SplitSequent.RuleApps] at this
      rcases this with this | this
      all_goals
        have ⟨φ, φ_in, φ_prop⟩ := this
        rcases φ <;> simp at φ_prop <;> grind [RuleApp.SplitSequents, f]
    case oStep q' q_in_cone' B_turn_q' g_in_moves_q' =>
      rcases q with ⟨Γ | R, Γs, Rs⟩ <;> simp at B_turn_q
      rcases q' with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at B_turn_q'
      simp [coalgebraGame] at g_in_moves_q'

theorem rewind_history_correspondence (Γ g) (strat : Strategy coalgebraGame Prover)
  (n) (h2 h3 h4 h6)  (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  : (∀ b_turn_g : coalgebraGame.turn g = Builder, f (builder_RuleApp (rewind_history g ⟨2 * n, h3⟩) (by have := @rewind_turn g ⟨2 * n, h3⟩; grind)) = g.2.1[n]'h6)
  ∧ (∀ p_turn_q : coalgebraGame.turn g = Prover,  f (builder_RuleApp (rewind_history g ⟨2 * n + 1, h4⟩) (by have := @rewind_turn g ⟨2 * n + 1, h4⟩; simp [p_turn_q] at this; grind)) = g.2.1[n]'h2)
  := by
  have rewind_one_step_in_cone := fun h ↦ rewind_history_one_step_in_cone g h strat in_cone
  have length := history_length_in_cone strat g in_cone
  · cases n
    case zero =>
      by_cases coalgebraGame.turn g = Prover
      case pos h =>
        simp [rewind_history, h]
        apply rewind_history_one_step_correspondence strat in_cone
      case neg h =>
        simp at h
        simp [h]
        cases in_cone <;> simp [coalgebraGame] at h
        case myStep q q_in_cone q_has_moves p_move_q =>
          have := (strat q p_move_q q_has_moves).2
          obtain ⟨Γ' | R, Γs, Rs⟩ := q <;> simp [coalgebraGame] at p_move_q
          simp [Game.Pos.moves, coalgebraGame, -SetLike.coe_mem, SplitSequent.RuleApps] at this
          rcases this with ⟨R, ⟨φ, φ_in, φ_prop⟩ | ⟨φ, φ_in, φ_prop⟩, R_prop⟩
          all_goals
            simp [←R_prop] at *
            simp [builder_RuleApp]
            cases φ <;> simp at φ_prop <;> grind [f]
        case oStep q q_in_cone b_move_q g_in_moves_q =>
        rcases q with ⟨Γ' | R, Γs, Rs⟩ <;> simp [coalgebraGame] at b_move_q
        simp [coalgebraGame, -SetLike.coe_mem, SplitSequent.RuleApps] at g_in_moves_q
        have ⟨R, _, _, R_prop⟩ := g_in_moves_q
        subst R_prop
        simp at h
    case succ n =>
    let info := g.1
    let Γs := g.2.1
    let Rs := g.2.2
    have g_def : g = ⟨info, Γs, Rs⟩ := by
      unfold info Γs Rs
      rfl
    rcases info with Γ' | R <;> simp [coalgebraGame]
    · have := @rewind_turn ⟨Sum.inl Γ', Γs, Rs⟩ ⟨2 * (n + 1) + 1, g_def ▸ h4⟩
      unfold rewind_history
      simp [rewind_history_one_step]
      have for_termination_1 : Γs.length + Rs.tail.length < Γs.length + Rs.length := by
        cases Rs_def : Rs <;> rw [g_def] at h4 <;> simp [coalgebraGame] at h4
        · simp_all
        · grind
      convert (rewind_history_correspondence Γ ⟨Sum.inr (Rs.head _) , Γs, Rs.tail⟩ strat (n + 1) _ _ _ _ _).1 _ using 1 <;> try grind
      · simp [coalgebraGame]
        simp [g_def, coalgebraGame] at h4
        simp [g_def, coalgebraGame] at length
        grind
      · simp [coalgebraGame]
        simp [g_def, coalgebraGame] at h4
        simp [g_def, coalgebraGame] at length
        grind
      · simp [g_def, coalgebraGame] at rewind_one_step_in_cone
        apply rewind_one_step_in_cone
        grind
      · simp [coalgebraGame]
    · have h : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      simp [h]
      unfold rewind_history
      simp [rewind_history_one_step]
      have for_termination_2 : Γs.tail.length + Rs.length < Γs.length + Rs.length := by
        cases Γs_def : Γs <;> rw [g_def] at h2
        · simp_all
          grind
        · grind
      convert (rewind_history_correspondence Γ ⟨Sum.inl (Γs.head _) , Γs.tail, Rs⟩ strat n _ _ _ _ _).2 _ using 1 <;> try grind
      · simp [g_def, coalgebraGame] at rewind_one_step_in_cone
        apply rewind_one_step_in_cone
        grind
      · simp [coalgebraGame]
termination_by g.2.1.length + g.2.2.length
decreasing_by
  · convert for_termination_1
  · convert for_termination_2

noncomputable -- this should be computable if we use Fin.find instead, but Fin.find is confusing me atm
def rep_next {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
    (h : winning strat ⟨Sum.inl Γ, [], []⟩) (rep : Δ ∈ g.1.2.1) : (btype Γ strat) :=
  ⟨rep_pos g rep,
   rewind_history_in_cone g.1 ⟨(2 * (List.mem_iff_get.1 rep).choose.1), _⟩ strat g.2.1,
    by
      have := @rewind_turn g.1 ⟨(2 * (List.mem_iff_get.1 rep).choose.1), by
        have length := history_length_in_cone strat g.1 g.2.1
        simp [g.2.2] at *
        have := (List.mem_iff_get.1 rep).choose.2
        grind⟩
      simp [g.2.2] at this
      convert this⟩


theorem rep_next_cor {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (rep : Δ ∈ g.1.2.1) :
  f (builder_RuleApp (rep_next g h rep).1 (rep_next g h rep).2.2) = Δ := by
  have Δ_eq := (List.mem_iff_get.1 rep).choose_spec
  conv =>
  · congr
    · skip
    · rw [←Δ_eq]
  let n := (List.mem_iff_get.1 rep).choose
  simp [rep_next, rep_pos]
  convert (rewind_history_correspondence Γ g.1 strat (List.mem_iff_get.1 rep).choose.1 _ _ _ _ g.2.1).1 _  <;> try grind
  have length := history_length_in_cone strat g.1 g.2.1
  simp [g.2.2] at *
  have := (List.mem_iff_get.1 rep).choose.2
  grind

noncomputable
def builder_children {Γ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
    (h : winning strat ⟨Sum.inl Γ, [], []⟩) : List (btype Γ strat) := match g_def : g with
  | ⟨⟨Sum.inl _, _, _⟩, x, y⟩ => False.elim (by unfold Game.turn at y; simp [coalgebraGame] at y)
  | ⟨⟨Sum.inr R, Γs, Rs⟩, _⟩ =>
    match R with
      | RuleApp.topₗ _ _ => []
      | RuleApp.topᵣ _ _ => []
      | RuleApp.axₗₗ _ _ _ => []
      | RuleApp.axₗᵣ _ _ _ => []
      | RuleApp.axᵣₗ _ _ _ => []
      | RuleApp.axᵣᵣ _ _ _ => []
      | RuleApp.orₗ Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {Sum.inl (φ1 v φ2)}) ∪ {Sum.inl φ1, Sum.inl φ2} ∈ Γs
          then [rep_next g h (by convert rep; grind)]
          else [next_next g h (by convert rep; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
      | RuleApp.orᵣ Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {Sum.inr (φ1 v φ2)}) ∪ {Sum.inr φ1, Sum.inr φ2} ∈ Γs
          then [rep_next g h (by convert rep; grind)]
          else [next_next g h (by convert rep; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
      | RuleApp.andₗ Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {Sum.inl (φ1 & φ2)}) ∪ {Sum.inl φ1} ∈ Γs
          then
            if rep2 : (Δ \ {Sum.inl (φ1 & φ2)}) ∪ {Sum.inl φ2} ∈ Γs
              then [rep_next g h (by convert rep1; grind), rep_next g h (by convert rep2; grind)]
              else [rep_next g h (by convert rep1; grind), next_next g h (by convert rep2; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
          else
            if rep2 : (Δ \ {Sum.inl (φ1 & φ2)}) ∪ {Sum.inl φ2} ∈ Γs
              then [next_next g h (by convert rep1; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp]), rep_next g h (by convert rep2; grind)]
              else [next_next g h (by convert rep1; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp]), next_next g h (by convert rep2; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
      | RuleApp.andᵣ Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {Sum.inr (φ1 & φ2)}) ∪ {Sum.inr φ1} ∈ Γs
          then
            if rep2 : (Δ \ {Sum.inr (φ1 & φ2)}) ∪ {Sum.inr φ2} ∈ Γs
              then [rep_next g h (by convert rep1; grind), rep_next g h (by convert rep2; grind)]
              else [rep_next g h (by convert rep1; grind), next_next g h (by convert rep2; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
          else
            if rep2 : (Δ \ {Sum.inr (φ1 & φ2)}) ∪ {Sum.inr φ2} ∈ Γs
              then [next_next g h (by convert rep1; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp]), rep_next g h (by convert rep2; grind)]
              else [next_next g h (by convert rep1; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp]), next_next g h (by convert rep2; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
      | RuleApp.boxₗ Δ φ φ_in =>
        if rep : (Δ \ {Sum.inl (□φ)}).D ∪ {Sum.inl φ} ∈ Γs
          then [rep_next g h (by convert rep; grind)]
          else [next_next g h (by convert rep; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]
      | RuleApp.boxᵣ Δ φ φ_in =>
        if rep : (Δ \ {Sum.inr (□φ)}).D ∪ {Sum.inr φ} ∈ Γs
          then [rep_next g h (by convert rep; grind)]
          else [next_next g h (by convert rep; grind) (by subst g_def; simp [RuleApp.SplitSequents, builder_RuleApp])]

theorem gameP_general {Γ : SplitSequent} (strat : Strategy coalgebraGame Prover)
    (h : winning strat ⟨Sum.inl Γ, [], []⟩) : ⊢ Γ := by
  use {
    X := btype Γ strat
    α g := ⟨builder_RuleApp g.1 g.2.2, builder_children g h⟩
    h := by  -- scary!!!!
      intro g
      rcases g_def : g with ⟨⟨Γ | R, Γs, Rs⟩, in_cone, b_move⟩
      · exfalso; simp [coalgebraGame] at b_move
      · subst g_def
        simp only [r, builder_RuleApp]
        cases R
        · simp only [p, builder_children]
          rfl
        · simp only [p, builder_children]
          rfl
        · simp only [p, builder_children]
          rfl
        · simp only [p, builder_children]
          rfl
        · simp only [p, builder_children]
          rfl
        · simp only [p, builder_children]
          rfl
        case andₗ Δ φ1 φ2 φ_in =>
          simp only [p, builder_children, List.map_eq_cons_iff, ↓existsAndEq,
            List.map_eq_nil_iff, true_and, and_true]
          by_cases Δ \ {Sum.inl (φ1 & φ2)} ∪ {Sum.inl φ1} ∈ Γs
          case pos rep1 =>
            by_cases Δ \ {Sum.inl (φ1 & φ2)} ∪ {Sum.inl φ2} ∈ Γs
            case pos rep2 =>
              simp only [rep1, rep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep1])
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep2])
            case neg nrep2 =>
              simp only [rep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep1])
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep2
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
          case neg nrep1 =>
            by_cases Δ \ {Sum.inl (φ1 & φ2)} ∪ {Sum.inl φ2} ∈ Γs
            case pos rep2 =>
              simp only [nrep1, rep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep1
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep2])
            case neg nrep2 =>
              simp only [nrep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, fₙ_alternate]
              constructor
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep1
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep2
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
        case andᵣ Δ φ1 φ2 φ_in =>
          simp only [p, builder_children, List.map_eq_cons_iff, ↓existsAndEq,
            List.map_eq_nil_iff, true_and, and_true]
          by_cases Δ \ {Sum.inr (φ1 & φ2)} ∪ {Sum.inr φ1} ∈ Γs
          case pos rep1 =>
            by_cases Δ \ {Sum.inr (φ1 & φ2)} ∪ {Sum.inr φ2} ∈ Γs
            case pos rep2 =>
              simp only [rep1, rep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep1])
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep2])
            case neg nrep2 =>
              simp only [rep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep1])
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep2
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
          case neg nrep1 =>
            by_cases Δ \ {Sum.inr (φ1 & φ2)} ∪ {Sum.inr φ2} ∈ Γs
            case pos rep2 =>
              simp only [nrep1, rep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep1
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  (by simp only [rep2])
            case neg nrep2 =>
              simp only [nrep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, fₙ_alternate]
              constructor
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep1
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep2
                  (by simp [RuleApp.SplitSequents, builder_RuleApp])
        case orₗ Δ φ1 φ2 φ_in =>
          simp only [p, builder_children, List.map_eq_singleton_iff]
          by_cases Δ \ {Sum.inl (φ1 v φ2)} ∪ {Sum.inl φ1, Sum.inl φ2} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [rep_next]
            exact rep_next_cor ⟨⟨Sum.inr (RuleApp.orₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
              (by simp only [rep])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [next_next, fₙ_alternate]
            exact next_next_cor ⟨⟨Sum.inr (RuleApp.orₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep
              (by simp [RuleApp.SplitSequents, builder_RuleApp])
        case orᵣ Δ φ1 φ2 φ_in =>
          simp only [p, builder_children, List.map_eq_singleton_iff]
          by_cases Δ \ {Sum.inr (φ1 v φ2)} ∪ {Sum.inr φ1, Sum.inr φ2} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [rep_next]
            exact rep_next_cor ⟨⟨Sum.inr (RuleApp.orᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
              (by simp only [rep])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [next_next, fₙ_alternate]
            exact next_next_cor ⟨⟨Sum.inr (RuleApp.orᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep
              (by simp [RuleApp.SplitSequents, builder_RuleApp])
        case boxₗ Δ φ1 φ_in =>
          simp only [p, builder_children, List.map_eq_singleton_iff]
          by_cases (Δ \ {Sum.inl (□φ1)}).D ∪ {Sum.inl φ1} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [rep_next]
            exact rep_next_cor ⟨⟨Sum.inr (RuleApp.boxₗ Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
              (by simp only [rep])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [next_next, fₙ_alternate]
            exact next_next_cor ⟨⟨Sum.inr (RuleApp.boxₗ Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep
              (by simp [RuleApp.SplitSequents, builder_RuleApp])
        case boxᵣ Δ φ1 φ_in =>
          simp only [p, builder_children, List.map_eq_singleton_iff]
          by_cases (Δ \ {Sum.inr (□φ1)}).D ∪ {Sum.inr φ1} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [rep_next]
            exact rep_next_cor ⟨⟨Sum.inr (RuleApp.boxᵣ Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
              (by simp only [rep])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [next_next, fₙ_alternate]
            exact next_next_cor ⟨⟨Sum.inr (RuleApp.boxᵣ Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep
              (by simp [RuleApp.SplitSequents, builder_RuleApp])}
  have turn_P : coalgebraGame.turn (Sum.inl Γ, [], []) = Prover := by simp [coalgebraGame]
  let next_move := strat ⟨Sum.inl Γ, [], []⟩ turn_P (winning_has_moves turn_P h)
  have turn_next_move_B : coalgebraGame.turn next_move.1 = Builder := by
    rcases next_move with ⟨⟨Γ' | R, Γs, Rs⟩, in_moves⟩
    · unfold Game.Pos.moves Game.moves at in_moves
      simp [coalgebraGame] at in_moves
    · unfold Game.Pos.moves Game.moves
      simp [coalgebraGame]
  have next_in_cone : inMyCone strat (Sum.inl Γ, [], []) next_move.1 := by
    apply inMyCone.myStep
    exact inMyCone.nil
  use ⟨next_move, next_in_cone, turn_next_move_B⟩
  rcases next_move with ⟨⟨Γ' | R, Γs, Rs⟩, in_moves⟩
  · unfold Game.Pos.moves Game.moves at in_moves
    simp [coalgebraGame] at in_moves
  · unfold Game.Pos.moves Game.moves at in_moves
    simp [coalgebraGame] at in_moves
    have ⟨in_rule, eq1, eq2⟩ := in_moves
    subst_eqs
    simp [SplitSequent.RuleApps] at in_rule
    rcases in_rule with ⟨φ, φ_in, φ_prop⟩ | ⟨φ, φ_in, φ_prop⟩
    all_goals
      cases φ <;> simp at φ_prop <;> grind [f, r, builder_RuleApp]
