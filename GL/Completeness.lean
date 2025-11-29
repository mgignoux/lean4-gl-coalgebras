import GL.Logic
import GL.Semantics
import GL.CoalgebraProof
import GL.AxiomBlame
import GL.Game
import GL.CoalgebraGame
/-
abbrev Builder := Player.A
abbrev Prover := Player.B

def Sequent.RuleApps (Γ : Sequent) : Finset RuleApp :=
  let f : Formula → Option RuleApp := fun φ ↦
    if φ_in : φ ∈ Γ then match φ with
    | ⊤ => RuleApp.top Γ φ_in
    | at n => if nφ_in : na n ∈ Γ then RuleApp.ax Γ n ⟨φ_in, nφ_in⟩ else none
    | ψ & χ => RuleApp.and Γ ψ χ φ_in
    | ψ v χ => RuleApp.or Γ ψ χ φ_in
    | □ ψ => RuleApp.box Γ ψ φ_in
    | _ => none
    else none
  Finset.filterMap f Γ (by
  intro φ ψ r φ_f ψ_f
  cases φ <;> cases ψ <;> grind [f])

def RuleApp.Sequents (R : RuleApp) : Finset Sequent := match R with
  | RuleApp.top _ _ => ∅
  | RuleApp.ax _ _ _ => ∅
  | RuleApp.and Δ φ ψ _ => {(Δ \ {φ & ψ}) ∪ {φ}, (Δ \ {φ & ψ}) ∪ {ψ}}
  | RuleApp.or Δ φ ψ _ => {(Δ \ {φ v ψ}) ∪ {φ, ψ}}
  | RuleApp.box Δ φ _ => {(Δ \ {□ φ}).D ∪ {φ}}

abbrev gamePos := (Sequent ⊕ RuleApp) × List Sequent × List RuleApp

inductive move : gamePos → gamePos → Prop
  | prover  {R Rs Γ Γs} : R ∈ Γ.RuleApps → move ⟨Sum.inl Γ, Γs, Rs⟩ ⟨Sum.inr R, Γ :: Γs, Rs⟩
  | builder {R Rs Γ Γs} : Γ ∈ R.Sequents → Γ ∉ Γs → move ⟨Sum.inr R, Γs, Rs⟩ ⟨Sum.inl Γ, Γs, R :: Rs⟩

theorem move_move_in_FL {g1 g2 : gamePos} (h1 : (g1.1.isLeft)) (h3 : (g2.1.isLeft))
(g1_g2 : Relation.ReflTransGen (Relation.Comp move move) g1 g2): g2.1.getLeft h3 ∈ (g1.1.getLeft h1).FL.powerset := by
  simp
  induction g1_g2
  case refl => exact Sequent.FL_refl
  case tail g2 g3 g1_g2 g2_g3 ih =>
    simp [Relation.Comp] at g2_g3
    rcases g2_g3 with ⟨Γ', Γs', Rs', g2_g, g_g3⟩ | ⟨R', Γs', Rs', g2_g, g_g3⟩
    · rcases g3 with ⟨Γ'' | R'', Γs'', Rs''⟩ <;> simp at h3
      cases g_g3
    · rcases g3 with ⟨Γ'' | R'', Γs'', Rs''⟩ <;> simp at h3
      cases g_g3
      rcases g2 with ⟨Γ | R, Γs, Rs⟩ <;> cases g2_g
      simp_all
      rename_i Γ''_R' R'_Γ _
      have ih := Sequent.FL_subset ih
      simp [Sequent.FL_idem] at ih
      apply trans ?_ ih
      rcases R' <;> simp only [RuleApp.Sequents, Finset.mem_singleton, Finset.notMem_empty, Finset.mem_insert] at Γ''_R'
      case or Δ φ ψ in_Δ =>
        subst Γ''_R'
        simp [Sequent.RuleApps] at R'_Γ
        have ⟨φ, φ_in, h⟩ := R'_Γ
        rcases φ <;> simp at h
        simp only [h.1, Sequent.FL, Finset.subset_iff,
          Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
        intro χ χ_cases
        rcases χ_cases with h|h|h <;> subst_eqs
        · exact ⟨χ, h.1, Formula.FL_refl⟩
        · exact ⟨φ v ψ, in_Δ, by simp [Formula.FL, Formula.FL_refl]⟩
        · exact ⟨φ v ψ, in_Δ, by simp [Formula.FL, Formula.FL_refl]⟩
      case and Δ φ ψ in_Δ=>
        rcases Γ''_R' with l | l <;> subst l
        all_goals
          simp [Sequent.RuleApps] at R'_Γ
          have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h
          simp only [h.1, Sequent.FL, Finset.subset_iff,
            Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
          intro χ χ_cases
          rcases χ_cases with h|h <;> subst_eqs
          · exact ⟨χ, h.1, Formula.FL_refl⟩
          · exact ⟨φ & ψ, in_Δ, by simp [Formula.FL, Formula.FL_refl]⟩
      case box Δ φ in_Δ =>
        subst Γ''_R'
        simp [Sequent.RuleApps] at R'_Γ
        have ⟨φ, φ_in, h⟩ := R'_Γ
        rcases φ <;> simp at h
        simp [Sequent.D, Finset.subset_iff, Sequent.FL, h.1]
        refine ⟨⟨_, h.1 ▸ φ_in, by simp [Formula.FL, h.2, Formula.FL_refl]⟩, ?_⟩
        intro χ χ_cases
        rcases χ_cases with h|h <;> subst_eqs
        · exact ⟨χ, h.1.1, Formula.FL_refl⟩
        · exact ⟨◇ χ, h, by simp [Formula.FL, Formula.FL_refl]⟩

/- This is the main helper for showing there is no infinite chain, we do it 'from prover'
because that is where the FL properties are more readily available, but in fact it could
be from prover or builder. -/
lemma no_inf_chain_from_prover (g : ℕ → gamePos)
  (g_rel : ∀ (n : ℕ), Function.swap move (g (n + 1)) (g n)) (h : (g 0).1.isLeft) : False := by
  rcases g0_def : g 0 with ⟨Γ | R, Γs, Rs⟩ <;> simp [g0_def] at h
  have f_helper : ∀ n, (g (2 * n)).1.isLeft = true := by
    intro n
    induction n
    case zero => simp [g0_def]
    case succ k ih =>
      rcases g2k_def : g (2 * k) with ⟨Γ | R, Γs, Rs⟩ <;> simp_all
      rcases g2k1_def : g (2 * k + 1) with ⟨Γ | R, Γs, Rs⟩
      · exfalso
        have := g_rel (2 * k)
        rw [g2k_def, g2k1_def] at this
        cases this
      · have := g_rel (2 * k)
        rw [g2k_def, g2k1_def] at this
        cases this
        rcases g2k2_def : g (2 * (k + 1)) with ⟨Γ | R, Γs, Rs⟩ <;> simp
        have := g_rel (2 * k + 1)
        have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [g2k1_def, h, g2k2_def] at this
        cases this

  let f : ℕ → Sequent := fun n ↦ (g (2 * n)).1.getLeft (f_helper n)

  have g0_gn : ∀ n, Relation.ReflTransGen move (g 0) (g n) := by
    intro n
    induction n
    case zero => exact Relation.ReflTransGen.refl
    case succ n ih => apply Relation.ReflTransGen.tail ih (g_rel n)

  have f_prop : ∀ n, f n ∈ Γ.FL.powerset := by
    intro n
    have := @move_move_in_FL (g 0) (g (2 * n)) (f_helper 0) (f_helper n) (by
      induction n
      case zero => simp; exact Relation.ReflTransGen.refl
      case succ n ih =>
        apply Relation.ReflTransGen.tail ih
        refine  ⟨g (2 * n + 1), g_rel (2 * n), ?_⟩
        have := g_rel (2 * n + 1)
        simp [Function.swap] at this
        grind)
    unfold f
    simp only [g0_def] at this
    exact this

  let sequents : (n : ℕ) → List Sequent := Nat.rec [] (fun n ih => f n :: ih)

  have seq_prop : ∀ n, sequents n ++ Γs = (g (2 * n)).2.1 := by
    intro n
    induction n
    case zero => simp [sequents, g0_def]
    case succ k ih =>
      unfold sequents f at *
      have := f_helper k
      rcases g2k_def : g (2 * k) with ⟨Γ | R, Γs, Rs⟩ <;> simp_all
      · rcases g2k1_def : g (2 * k + 1) with ⟨Γ | R, Γs, Rs⟩
        · exfalso
          have := g_rel (2 * k)
          rw [g2k_def, g2k1_def] at this
          cases this
        · have := g_rel (2 * k)
          rw [g2k_def, g2k1_def] at this
          cases this
          rcases g2k2_def : g (2 * (k + 1)) with ⟨Γ | R, Γs, Rs⟩
          · have := g_rel (2 * k + 1)
            have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
            rw [g2k1_def, h, g2k2_def] at this
            cases this
            simp
          · have := g_rel (2 * k + 1)
            have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
            rw [g2k1_def, h, g2k2_def] at this
            cases this

  have seq_prop2 : ∀ n m, n < m → f n ∈ sequents m := by
    intro n m n_m
    induction m
    case zero => simp at n_m
    case succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 n_m with lt | eq
      · simp_all [sequents]
      · subst eq
        simp [sequents]

  have inf : Infinite {Δ // Δ ∈ Γ.FL.powerset} := by
    apply Infinite.of_injective (fun n ↦ ⟨f n, f_prop n⟩)
    intro n1 n2 hyp
    rcases Nat.lt_trichotomy n1 n2 with lt | eq | gt
    · exfalso
      have in_seq := seq_prop2 _ _ lt
      have := g_rel (2 * n2 - 1)
      rcases g2k2_def : g (2 * n2) with ⟨Γ | R, Γs, Rs⟩ <;> try grind
      have h : 2 * n2 - 1 + 1 = 2 * n2 := by grind
      rw [h, g2k2_def] at this
      rcases g2k21_def : g (2 * n2 - 1) with ⟨Γ | R, Γs, Rs⟩
      · rw [g2k21_def] at this
        cases this
      · rw [g2k21_def] at this
        cases this
        case builder not_in =>
          apply not_in
          have h : f n2 = Γ := by unfold f; simp [g2k2_def]
          have := seq_prop n2
          simp at hyp
          simp [g2k2_def] at this
          simp [← this, ← h, ← hyp, in_seq]
    · exact eq
    · exfalso
      have in_seq := seq_prop2 _ _ gt
      have := g_rel (2 * n1 - 1)
      rcases g2k2_def : g (2 * n1) with ⟨Γ | R, Γs, Rs⟩ <;> try grind
      have h : 2 * n1 - 1 + 1 = 2 * n1 := by grind
      rw [h, g2k2_def] at this
      rcases g2k21_def : g (2 * n1 - 1) with ⟨Γ | R, Γs, Rs⟩
      · rw [g2k21_def] at this
        cases this
      · rw [g2k21_def] at this
        cases this
        case builder not_in =>
          apply not_in
          have h : f n1 = Γ := by unfold f; simp [g2k2_def]
          have := seq_prop n1
          simp at hyp
          simp [g2k2_def] at this
          simp [← this, ← h, hyp, in_seq]
  apply inf.not_finite
  apply Set.finite_coe_iff.1
  apply Finset.finite_toSet

lemma matchesFinite : WellFounded (Function.swap move) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hyp
  simp at hyp
  rcases hyp with ⟨g, g_rel⟩
  simp only [Function.swap] at g_rel
  rcases g0_def : g 0 with ⟨Γ | R, Γs, Rs⟩
  · apply no_inf_chain_from_prover g g_rel (by simp_all)
  · have := g_rel 0
    rcases g1_def : g 1 with ⟨Γ | R, Γs, Rs⟩
    · simp [g0_def, g1_def] at this
      cases this
      apply no_inf_chain_from_prover (fun n ↦ g (n + 1)) (fun n ↦ g_rel (n + 1)) (by simp_all)
    · simp [g0_def, g1_def] at this
      cases this

def coalgebraGame : Game where
  Pos := gamePos
  turn
    | ⟨Sum.inl _, _, _⟩ => Prover
    | ⟨Sum.inr _, _, _⟩ => Builder
  moves
    | ⟨Sum.inl Γ, Γs, Rs⟩ => Finset.map ⟨fun R ↦ ⟨Sum.inr R, Γ :: Γs, Rs⟩, by intro r1 r2; simp⟩ Γ.RuleApps
    | ⟨Sum.inr R, Γs, Rs⟩ => Finset.filterMap (fun Γ ↦ if Γ ∈ Γs then none else some ⟨Sum.inl Γ, Γs, R :: Rs⟩) R.Sequents (by grind)
  wf := ⟨fun x y ↦ move y x, matchesFinite⟩
  move_rel := by
    intro ⟨info, Γs, Rs⟩ ⟨info', Γs', Rs'⟩ hyp
    rcases info with Γ | R
    · simp at hyp
      have ⟨R, R_prop, eq1, eq2, eq3⟩ := hyp
      subst_eqs
      simp
      apply move.prover R_prop
    · simp at hyp
      have ⟨Γ, Γ_prop, nin, eq1, eq2, eq3⟩ := hyp
      subst_eqs
      simp
      apply move.builder Γ_prop nin

#eval List.get [1,2,3,4,5,6] ⟨4, by simp⟩
#eval List.drop 4 [1,2,3,4,5,6]

-/
def btype (Γ : Sequent) (strat : Strategy coalgebraGame Prover) :=
 {g // inMyCone strat ⟨Sum.inl Γ, [], []⟩ g ∧ coalgebraGame.turn g = Builder}

def builder_RuleApp (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Builder) : RuleApp := match g with
  | ⟨Sum.inr R, _, _⟩ => R
  | ⟨Sum.inl _, _, _⟩ => False.elim (by simp_all [coalgebraGame])

-- maybe helpful?
theorem in_cone_winning {G : Game} {i : Player} {g g' : G.Pos} {strat : Strategy G i}
  (in_cone : inMyCone strat g g') (h : winning strat g) : winning strat g' := by
  induction in_cone
  case nil => exact h
  case myStep q q_in_cone has_moves my_turn ih =>
    apply winning_of_winning_move
    exact ih
  case oStep q q' q_in_cone o_turn in_moves ih =>
    exact @winning_of_whatever_other_move G i strat q o_turn ih ⟨q', in_moves⟩

def next_next {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (nrep : Δ ∉ g.1.2.1) (pos : Δ ∈ (builder_RuleApp g.1 g.2.2).Sequents) : btype Γ strat :=
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
  ⟨next_next, next_next_in_cone, B_next_next⟩

theorem next_next_cor {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (nrep : Δ ∉ g.1.2.1) (pos : Δ ∈ (builder_RuleApp g.1 g.2.2).Sequents) :
  f (builder_RuleApp (next_next g h nrep pos).1 (next_next g h nrep pos).2.2) = Δ := by
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
  simp [Sequent.RuleApps] at R_prop
  have ⟨φ, φ_in, φ_prop⟩ := R_prop
  cases φ <;> simp at φ_prop
  case atom =>
    have ⟨_, φ_prop⟩ := φ_prop
    subst φ_prop
    simp [f]
  all_goals
    subst φ_prop
    simp [f] -- most stupid proof ever!!!!!

theorem history_length_in_cone {Γ : Sequent} {strat : Strategy coalgebraGame Prover} (g : coalgebraGame.Pos)
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

def reconstruct_history {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (g : coalgebraGame.Pos) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g) (n : Nat) (lt : n < 2 * g.2.1.length + 1)
  : coalgebraGame.Pos :=
  if Even n then match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => ⟨Sum.inl $ (Γ :: Γs).get ⟨Γs.length - n/2, by sorry⟩, Γs.drop (Γs.length - n/2), Rs.drop (Rs.length - n/2)⟩
  | ⟨Sum.inr R, Γs, Rs⟩ => ⟨Sum.inr $ (R :: Rs).get ⟨Rs.length - n/2, by sorry⟩, Γs.drop (Γs.length - 1 - n/2), Rs.drop (Rs.length - n/2)⟩
  else match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => ⟨Sum.inr $ Rs.get ⟨Rs.length - 1 - n/2, by sorry⟩, Γs.drop (Γs.length - n/2), Rs.drop (Rs.length - n/2)⟩
  | ⟨Sum.inr R, Γs, Rs⟩ => ⟨Sum.inl $ Γs.get ⟨Γs.length - 1 - n/2, by sorry⟩, Γs.drop (Γs.length - 1 - n/2), Rs.drop (Rs.length - n/2)⟩


/-
r, 5, 5 =>
-----
l, 0, 0 --- step 0 => (5r[4], 5l.drop [4], 5r.drop [4])
r, 1, 0 --- step 1 => (5r[4], 5l.drop [3], 5r.drop [4])
l, 1, 1 --- step 2
r, 2, 1 --- step 3
-/

-- theorem reconstruct_history_in_cone {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
--   (h : winning strat ⟨Sum.inl Γ, [], []⟩) (g : coalgebraGame.Pos) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g) (n : Nat) (lt : n + 1 < 2 * g.2.1.length + 1)
--     : inMyCone strat ⟨Sum.inl Γ, [], []⟩ (reconstruct_history h g in_cone n (by omega)) := by
--   by_cases Even n
--   case pos even =>
--     have odd : ¬ Even (n + 1) := by grind
--     induction in_cone
--     case nil =>
--       simp [reconstruct_history, even]
--       apply inMyCone.nil
--     case myStep q q_in_cone q_has_moves p_turn_q ih =>
--       have in_moves := Subtype.prop (strat q p_turn_q q_has_moves)
--       rcases q with ⟨Γ | R, Γs, Rs⟩ <;> simp [coalgebraGame] at p_turn_q
--       unfold Game.Pos.moves Game.moves at in_moves
--       simp only [coalgebraGame, Finset.mem_map] at in_moves
--       have ⟨R, R_Γ, R_prop⟩ := in_moves
--       simp at R_prop
--       simp [←R_prop]
--       have ih := ih (by sorry)
--       simp_all [reconstruct_history]
--       have := inMyCone.myStep ih (by sorry) (by simp [coalgebraGame])
--       convert this

--       have ⟨⟨info, Γs, Rs⟩, in_moves⟩ := (strat ⟨Sum.inl Γ, Γs, Rs⟩ p_turn_q q_has_moves)


theorem reconstruct_history_moves {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (g : coalgebraGame.Pos) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g) (n : Nat) (lt : n + 1 < 2 * g.2.1.length + 1)
    : move (reconstruct_history h g in_cone n (by omega)) (reconstruct_history h g in_cone (n + 1) lt) := by
  by_cases Even n
  case pos even =>
    have odd : ¬ Even (n + 1) := by grind
    rcases g with ⟨Γ | R, Γs, Rs⟩
    · simp [even, odd, reconstruct_history]
      have := @move.prover (Rs[Rs.length - 1 - (n + 1) / 2]'(by sorry)) (List.drop (Rs.length - n / 2) Rs) Γs[Γs.length - 1 - n / 2] (List.drop (Γs.length - n / 2) Γs) (by sorry)

      have h1 : Γs[Γs.length - 1 - n / 2]'(by sorry) :: List.drop (Γs.length - n / 2) Γs = List.drop (Γs.length - (n + 1) / 2) Γs := by
        induction Γs
        case nil => simp at lt
        case cons Γ Γs ih =>
          -- simp
          -- have ih := ih (by sorry) (by sorry) (by sorry)
          -- have h1 := @List.drop_cons _ (Γs.length + 1 - (n + 1) / 2) Γ Γs (by sorry)
          -- have h2 := @List.drop_cons _ (Γs.length + 1 - n / 2) Γ Γs (by sorry)
          -- -- have h : (Γ :: Γs)[Γs.length - n / 2] :: List.drop (Γs.length + 1 - n / 2) (Γ :: Γs) = Γs[Γs.length - 1 - n / 2]'(by sorry) :: List.drop (Γs.length - n / 2) Γs :=  by sorry
          -- rw [h1, h2]
          sorry
      have h2 : List.drop (Rs.length - n / 2) Rs = List.drop (Rs.length - (n + 1) / 2) Rs := by
        apply congrArg₂ <;> try rfl
        apply congrArg₂ <;> try rfl
        sorry -- very doable
      rw [←h1, ←h2]

      -- exact this
      sorry
    · sorry
  case neg odd => sorry

    --rcases (strat ⟨Sum.inl Γ, Γs, Rs⟩ p_turn_q q_has_moves) with ⟨⟨Γ | R, Γs, Rs⟩, in_moves⟩



-- theorem reconstruct_history_is_valid_moves {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
--   (h : winning strat ⟨Sum.inl Γ, [], []⟩) (g : coalgebraGame.Pos) (n : Nat)
--   : reconstruct_history.Pos :=


#exit

noncomputable
def rep_pos {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
 (rep : Δ ∈ g.1.2.1) : coalgebraGame.Pos :=
  let ⟨n, n_prop⟩ := (List.mem_iff_get.1 rep).choose
  ⟨Sum.inr ((builder_RuleApp g.1 g.2.2 :: g.1.2.2).get ⟨n, by sorry⟩), g.1.2.1.drop n, g.1.2.2.drop n⟩

-- theorem rewind_history_in_cone {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
--   (h : winning strat ⟨Sum.inl Γ, [], []⟩) (g : coalgebraGame.Pos) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g) (n : Fin (2 * g.2.2.length + 1))
--     : inMyCone strat ⟨Sum.inl Γ, [], []⟩ (rewind_history h g n) := by
--     unfold rewind_history
--     induction n using Fin.reverseInduction
--     case last =>
--       simp
--       rcases g with ⟨Γ' | R, Γs, Rs⟩
--       · have h : Rs.length = Γs.length := by sorry
--         simp_all
--         convert @inMyCone.nil _ _ strat ⟨Sum.inl Γ, [], []⟩
--         · sorry
--         · simp [h]
--       · have h : Rs.length + 1 = Γs.length := by sorry
--         simp_all
--         have := @inMyCone.myStep _ _ strat _ _ (@inMyCone.nil _ _ strat ⟨Sum.inl Γ, [], []⟩) (by sorry) (by simp [coalgebraGame])
--         convert this
--         · sorry
--     case cast n ih =>
--       simp_all
--       by_cases h : Even n.1
--       · rcases g with ⟨Γ' | R, Γs, Rs⟩
--         · simp [h]
--           have h : ¬ Even (n.1 + 1) := by grind
--           simp [h] at ih
--           have := fun r ↦ @inMyCone.oStep _ _ strat _ _ r ih (by simp [coalgebraGame])
--           apply this
--           simp [coalgebraGame]
--           refine ⟨?_, ?_, ?_⟩
--           · sorry
--           · sorry
--           · sorry
--         · sorry
--       · sorry

theorem rep_in_cone {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (rep : Δ ∈ g.1.2.1) :
    inMyCone strat (Sum.inl Γ, [], []) (rep_pos g rep) := by
    cases g_len : g.1.2.1.length
    case zero =>
      unfold rep_pos
      have ⟨n, n_prop⟩ := (List.mem_iff_get.1 rep).choose
      simp [g_len] at n_prop
    case succ k =>
    unfold rep_pos
    have n := (List.mem_iff_get.1 rep).choose
    simp [g_len] at n
    induction n using Fin.reverseInduction
    case last =>
      -- have h : g.1.2.1.length = n := by omega
      -- subst h
      simp
      rcases g with ⟨⟨Γ | R, Γs, Rs⟩, in_cone, b_move⟩
      · simp [coalgebraGame] at b_move
      · have h : @Fin.val Γs.length (List.mem_iff_get.1 rep).choose = Rs.length := by sorry
        simp_all [builder_RuleApp]
        have h : Rs.length + 1 = Γs.length := by sorry
        have h1 : List.drop Rs.length Γs = [Γs.getLast (by sorry)] := by sorry
        have h2 : (R :: Rs)[Rs.length] = Rs.getLast (by sorry) := by sorry
        simp [h1, h2]
        convert @inMyCone.myStep _ _ strat _ _ (@inMyCone.nil _ _ strat ⟨Sum.inl Γ, [], []⟩) (by sorry) (by simp [coalgebraGame])
        sorry
    case cast n ih =>
      simp_all -- suspicious

noncomputable -- this should be computable if we use Fin.find instead, but Fin.find is confusing me atm
def rep_next {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
    (h : winning strat ⟨Sum.inl Γ, [], []⟩) (rep : Δ ∈ g.1.2.1) : (btype Γ strat) :=
  ⟨rep_pos g rep, rep_in_cone g h rep, by sorry⟩ -- last sorry is easy just needs a helper
  -- choose rep_next with strat?
  -- let rep_next : gamePos := ⟨Sum.inr (g.1.2.2.get ⟨n, by sorry⟩), g.1.2.1.drop n, g.1.2.2.drop n⟩
  -- have B_rep_next : coalgebraGame.turn rep_next = Builder := by unfold Game.turn rep_next; simp [coalgebraGame]
  -- have rep_next_in_cone : inMyCone strat (Sum.inl Γ, [], []) rep_next := by sorry
  -- ⟨rep_next, rep_next_in_cone, B_rep_next⟩

theorem rep_next_cor {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (rep : Δ ∈ g.1.2.1) (pos : Δ ∈ (builder_RuleApp g.1 g.2.2).Sequents) :
  f (builder_RuleApp (rep_next g h rep).1 (rep_next g h rep).2.2) = Δ := by
  let ⟨n, n_lt⟩ := (List.mem_iff_get.1 rep).choose
  have n_prop := (List.mem_iff_get.1 rep).choose_spec
  simp [rep_next, rep_pos, builder_RuleApp]
  rcases g with ⟨⟨Γ | R, Γs, Rs⟩, in_cone, b_move⟩ <;> simp [coalgebraGame] at b_move
  simp_all
  cases (List.mem_iff_get.1 rep).choose.1 -- using Fin.reverseInduction
  simp


  rw [←n_prop]
  sorry
  --⟨Sum.inr ((builder_RuleApp g.1 g.2.2 :: g.1.2.2).get ⟨n, by sorry⟩), g.1.2.1.drop n, g.1.2.2.drop n⟩


--- dont do this! define a function which gets the sequents starting from the beginning sequen to g, then show that each of those sequents is (1) in the cone, and (2) moves from one to the next, then you have what you want a lot easier!

noncomputable
def builder_children {Γ : Sequent} {strat : Strategy coalgebraGame Prover} (g : btype Γ strat)
    (h : winning strat ⟨Sum.inl Γ, [], []⟩) : List (btype Γ strat) := match g_def : g with
  | ⟨⟨Sum.inl _, _, _⟩, x, y⟩ => False.elim (by unfold Game.turn at y; simp [coalgebraGame] at y)
  | ⟨⟨Sum.inr R, Γs, Rs⟩, _⟩ =>
    match R with
      | RuleApp.top _ _ => []
      | RuleApp.ax _ _ _ => []
      | RuleApp.or Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {φ1 v φ2}) ∪ {φ1, φ2} ∈ Γs
          then [rep_next g h (by convert rep; grind)]
          else [next_next g h (by convert rep; grind) (by subst g_def; simp [RuleApp.Sequents, builder_RuleApp])]
      | RuleApp.and Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {φ1 & φ2}) ∪ {φ1} ∈ Γs
          then
            if rep2 : (Δ \ {φ1 & φ2}) ∪ {φ2} ∈ Γs
              then [rep_next g h (by convert rep1; grind), rep_next g h (by convert rep2; grind)]
              else [rep_next g h (by convert rep1; grind), next_next g h (by convert rep2; grind) (by subst g_def; simp [RuleApp.Sequents, builder_RuleApp])]
          else
            if rep2 : (Δ \ {φ1 & φ2}) ∪ {φ2} ∈ Γs
              then [next_next g h (by convert rep1; grind) (by subst g_def; simp [RuleApp.Sequents, builder_RuleApp]), rep_next g h (by convert rep2; grind)]
              else [next_next g h (by convert rep1; grind) (by subst g_def; simp [RuleApp.Sequents, builder_RuleApp]), next_next g h (by convert rep2; grind) (by subst g_def; simp [RuleApp.Sequents, builder_RuleApp])]
      | RuleApp.box Δ φ φ_in =>
        if rep : (Δ \ {□φ}).D ∪ {φ} ∈ Γs
          then [rep_next g h (by convert rep; grind)]
          else [next_next g h (by convert rep; grind) (by subst g_def; simp [RuleApp.Sequents, builder_RuleApp])]

theorem gameP_general {Γ : Sequent} (strat : Strategy coalgebraGame Prover)
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
        · simp only [p, builder_children]
        case and Δ φ1 φ2 φ_in =>
          simp only [p, builder_children, List.map_eq_cons_iff, ↓existsAndEq,
            List.map_eq_nil_iff, true_and, and_true]
          by_cases Δ \ {φ1 & φ2} ∪ {φ1} ∈ Γs
          case pos rep1 =>
            by_cases Δ \ {φ1 & φ2} ∪ {φ2} ∈ Γs
            case pos rep2 =>
              simp only [rep1, rep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h rep1
                  (by simp [RuleApp.Sequents, builder_RuleApp])
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h rep2
                  (by simp [RuleApp.Sequents, builder_RuleApp])
            case neg nrep2 =>
              simp only [rep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h rep1
                  (by simp [RuleApp.Sequents, builder_RuleApp])
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep2
                  (by simp [RuleApp.Sequents, builder_RuleApp])
          case neg nrep1 =>
            by_cases Δ \ {φ1 & φ2} ∪ {φ2} ∈ Γs
            case pos rep2 =>
              simp only [nrep1, rep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep1
                  (by simp [RuleApp.Sequents, builder_RuleApp])
              · exact rep_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h rep2
                  (by simp [RuleApp.Sequents, builder_RuleApp])
            case neg nrep2 =>
              simp only [nrep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true, ↓existsAndEq, true_and, rep_next, fₙ_alternate]
              constructor
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep1
                  (by simp [RuleApp.Sequents, builder_RuleApp])
              · exact next_next_cor ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep2
                  (by simp [RuleApp.Sequents, builder_RuleApp])
        case or Δ φ1 φ2 φ_in =>
          simp only [p, builder_children, List.map_eq_singleton_iff]
          by_cases Δ \ {φ1 v φ2} ∪ {φ1, φ2} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [rep_next]
            exact rep_next_cor ⟨⟨Sum.inr (RuleApp.or Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h rep
              (by simp [RuleApp.Sequents, builder_RuleApp])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [next_next, fₙ_alternate]
            exact next_next_cor ⟨⟨Sum.inr (RuleApp.or Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep
              (by simp [RuleApp.Sequents, builder_RuleApp])
        case box Δ φ1 φ_in =>
          simp only [p, builder_children, List.map_eq_singleton_iff]
          by_cases (Δ \ {□φ1}).D ∪ {φ1} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [rep_next]
            exact rep_next_cor ⟨⟨Sum.inr (RuleApp.box Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h rep
              (by simp [RuleApp.Sequents, builder_RuleApp])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [next_next, fₙ_alternate]
            exact next_next_cor ⟨⟨Sum.inr (RuleApp.box Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h nrep
              (by simp [RuleApp.Sequents, builder_RuleApp])
  }
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
    simp [Sequent.RuleApps] at in_rule
    have ⟨φ, φ_in, φ_prop⟩ := in_rule
    cases φ <;> simp at φ_prop
    case atom => -- have to find the second 'principal' formula
      have ⟨_, φ_prop⟩ := φ_prop
      subst φ_prop
      simp [f, r, builder_RuleApp]
    all_goals
      subst φ_prop
      simp [f, r, builder_RuleApp]


/-
theorem gameP_general' {Γ : Sequent} {Γs : List Sequent} {Rs : List RuleApp} (strat : Strategy coalgebraGame Prover)
    (h : winning strat ⟨Sum.inl Γ, Γs, Rs⟩) : ⊢ Γ := by
  have P_turn : coalgebraGame.turn ⟨Sum.inl Γ, Γs, Rs⟩ = Prover := by unfold Game.turn; simp [coalgebraGame]
  let next_move := strat ⟨Sum.inl Γ, Γs, Rs⟩ P_turn
    (by by_contra hyp; exfalso; unfold winning winner at h; simp_all)
  have still_winning_next : winning strat next_move := winning_of_winning_move P_turn h
  have still_winning_next_next := @winning_of_whatever_other_move coalgebraGame Prover strat next_move (by sorry) still_winning_next
  rcases next_move_def : next_move with ⟨⟨info, Γs', Rs'⟩, in_moves⟩
  simp [coalgebraGame, Game.Pos.moves, Game.moves, Sequent.RuleApps] at in_moves
  -- by_cases Γ ∈ Γs
  -- case pos rep => simp [rep] at in_moves
  -- case neg nrep =>
  -- simp [nrep] at in_moves
  have ⟨R, ⟨φ, φ_in_Γ, φ_prop⟩, eq1, eq2, eq3⟩ := in_moves
  clear in_moves
  rcases φ <;> simp_all
  case top =>
    use {
    X := Unit
    α u := ⟨RuleApp.top Γ φ_in_Γ, []⟩
    h := by simp only [r, p, implies_true]}
    use ()
    simp [f, r]
  case atom n =>
    use {
    X := Unit
    α u := ⟨RuleApp.ax Γ n ⟨φ_in_Γ, by grind⟩, []⟩
    h := by simp only [r, p, implies_true]}
    use ()
    simp [f, r]
  case and φ1 φ2 =>
    subst φ_prop
    let next_next_move : gamePos := ⟨Sum.inl $ (Γ \ {φ1 & φ2}) ∪ {φ1}, Γs', RuleApp.and Γ φ1 φ2 φ_in_Γ :: Rs⟩
    have P_turn_next_next_move : coalgebraGame.turn next_next_move = Prover := by unfold Game.turn next_next_move; simp [coalgebraGame]
    have next_next_in_moves : next_next_move ∈ coalgebraGame.moves (Sum.inr (RuleApp.and Γ φ1 φ2 φ_in_Γ), Γ :: Γs, Rs) := by
      unfold next_next_move
      simp [coalgebraGame, RuleApp.Sequents, eq2]
    have still_winning_next_next' : winning strat next_next_move := by
      apply still_winning_next_next
      simp_all
    have ⟨𝕐1, y1, y1_prop⟩ := gameP_general strat still_winning_next_next'
    let next_next_move : gamePos := ⟨Sum.inl $ (Γ \ {φ1 & φ2}) ∪ {φ2}, Γs', RuleApp.and Γ φ1 φ2 φ_in_Γ :: Rs⟩
    have P_turn_next_next_move : coalgebraGame.turn next_next_move = Prover := by unfold Game.turn next_next_move; simp [coalgebraGame]
    have next_next_in_moves : next_next_move ∈ coalgebraGame.moves (Sum.inr (RuleApp.and Γ φ1 φ2 φ_in_Γ), Γ :: Γs, Rs) := by
      unfold next_next_move
      simp [coalgebraGame, RuleApp.Sequents, eq2]
    have still_winning_next_next : winning strat next_next_move := by
      apply still_winning_next_next
      simp_all
    have ⟨𝕐2, y2, y2_prop⟩ := gameP_general strat still_winning_next_next'
    use {
    X := 𝕐1.X ⊕ 𝕐2.X ⊕ Unit
    α
      | Sum.inl z => T.map (Sum.inl) (𝕐1.α z)
      | Sum.inr (Sum.inl z) => T.map (fun x ↦ Sum.inr (Sum.inl x)) (𝕐2.α z)
      | Sum.inr (Sum.inr u) => ⟨RuleApp.and Γ φ1 φ2 φ_in_Γ, [Sum.inl y1, Sum.inr (Sum.inl y2)]⟩
    h := by sorry}
    use Sum.inr (Sum.inr ())
    simp [f, r]
  case or φ1 φ2 =>
    by_cases (Γ \ {φ1 v φ2}) ∪ {φ1, φ2} ∈ Γs'
    case pos h => -- builder has instantly won the game
      -- have ⟨⟨n, n_lt⟩, n_prop⟩ := List.mem_iff_get.1 h
      sorry -- we are done playing the game here! we have everything to build the proof!
    case neg nin =>
      subst φ_prop
      let next_next_move : gamePos := ⟨Sum.inl $ (Γ \ {φ1 v φ2}) ∪ {φ1, φ2}, Γs', RuleApp.or Γ φ1 φ2 φ_in_Γ :: Rs⟩
      have P_turn_next_next_move : coalgebraGame.turn next_next_move = Prover := by unfold Game.turn next_next_move; simp [coalgebraGame]
      have next_next_in_moves : next_next_move ∈ coalgebraGame.moves (Sum.inr (RuleApp.or Γ φ1 φ2 φ_in_Γ), Γ :: Γs, Rs) := by
        unfold next_next_move
        simp [coalgebraGame, RuleApp.Sequents, eq2, -Finset.insert_union, -Finset.singleton_union,  -Finset.union_insert]
      have still_winning_next_next' : winning strat next_next_move := by
        apply still_winning_next_next
        simp_all
      have ⟨𝕐, y, y_prop⟩ := gameP_general strat still_winning_next_next'
      use {
      X := 𝕐.X ⊕ Unit
      α
        | Sum.inl z => T.map (Sum.inl) (𝕐.α z)
        | Sum.inr u => ⟨RuleApp.or Γ φ1 φ2 φ_in_Γ, [Sum.inl y]⟩
      h := by sorry}
      use Sum.inr ()
      simp [f, r]
  case box φ1 =>
    subst φ_prop
    let next_next_move : gamePos := ⟨Sum.inl $ (Γ \ {□ φ1}).D ∪ {φ1}, Γs', RuleApp.box Γ φ1 φ_in_Γ :: Rs⟩
    have P_turn_next_next_move : coalgebraGame.turn next_next_move = Prover := by unfold Game.turn next_next_move; simp [coalgebraGame]
    have next_next_in_moves : next_next_move ∈ coalgebraGame.moves (Sum.inr (RuleApp.box Γ φ1 φ_in_Γ), Γ :: Γs, Rs) := by
      unfold next_next_move
      simp [coalgebraGame, RuleApp.Sequents, eq2, -Finset.insert_union, -Finset.union_singleton]
    have still_winning_next_next' : winning strat next_next_move := by
      apply still_winning_next_next
      simp_all
    have ⟨𝕐, y, y_prop⟩ := gameP_general strat still_winning_next_next'
    use {
    X := 𝕐.X ⊕ Unit
    α
      | Sum.inl z => T.map (Sum.inl) (𝕐.α z)
      | Sum.inr u => ⟨RuleApp.box Γ φ1 φ_in_Γ, [Sum.inl y]⟩
    h := by sorry}
    use Sum.inr ()
    simp [f, r]
termination_by
  (WellFounded.transGen $ coalgebraGame.wf.2).wrap ⟨Sum.inl Γ, Γs, Rs⟩
decreasing_by
  all_goals
    apply @Relation.TransGen.tail _ _ _ next_move.1
    · apply Relation.TransGen.single
      apply coalgebraGame.move_rel
      simp only [WellFounded.wrap, next_move_def]
      unfold next_next_move at next_next_in_moves
      subst_eqs
      exact next_next_in_moves
    · apply coalgebraGame.move_rel
      simp [WellFounded.wrap]
-/

def after_box (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inl _, _, R :: _⟩ => R.isBox
  | _ => false

def prover_sequent (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover) : Sequent := match g_def : g with
  | ⟨Sum.inl Δ, _, _⟩ => Δ
  | ⟨Sum.inr _, _, _⟩ => False.elim (by simp_all [coalgebraGame])

def gameB_model_type {Γ : Sequent} {Γs : List Sequent} {Rs : List RuleApp}
  (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Γ, Γs, Rs⟩)
  : Type :=
  let in_cone := @inMyCone Builder coalgebraGame strat ⟨Sum.inl Γ, Γs, Rs⟩
  {g : coalgebraGame.Pos // (after_box g ∧ in_cone g) ∨ g = ⟨Sum.inl Γ, Γs, Rs⟩}

def gameB_model {Γ : Sequent} {Γs : List Sequent} {Rs : List RuleApp}
  (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Γ, Γs, Rs⟩)
  : Model (gameB_model_type strat h) where
  V g n := at n ∉ prover_sequent g.1 (by sorry) -- not quite right
  R := fun g1 g2 ↦ Relation.TransGen move g1.1 g2.1
  trans := by intro g1 g2 g3 g1_g2 g2_g3; exact Relation.TransGen.trans g1_g2 g2_g3
  con_wf := by sorry -- this is all very doable


theorem gameB_model_sat {Γ : Sequent} {Γs : List Sequent} {Rs : List RuleApp}
  (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Γ, Γs, Rs⟩) :
  ∀ φ ∈ Γ, ¬ Evaluate ⟨gameB_model strat h, ⟨⟨Sum.inl Γ, Γs, Rs⟩, by simp⟩⟩ φ := by
    have P_turn : coalgebraGame.turn ⟨Sum.inl Γ, Γs, Rs⟩ = Prover := by unfold Game.turn; simp [coalgebraGame]
    intro φ φ_in
    cases φ
    case bottom => simp_all
    case top => -- if its top then builder cannot have a winning strategy
      let next_move : gamePos := ⟨Sum.inr (RuleApp.top Γ φ_in), Γ :: Γs, Rs⟩
      have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
      have next_in_moves : next_move ∈ coalgebraGame.moves ⟨Sum.inl Γ, Γs, Rs⟩ := by
        unfold next_move
        simp [coalgebraGame, Sequent.RuleApps]
        refine ⟨⊤, φ_in, by simp⟩
      have still_winning_next : winning strat next_move := by
        exact winning_of_whatever_other_move P_turn h ⟨next_move, next_in_moves⟩ -- removing by exact doesn't work ?
      have has_moves := winning_has_moves B_turn_next still_winning_next
      unfold Game.moves next_move at has_moves
      simp [coalgebraGame, RuleApp.Sequents] at has_moves
    case atom n => simp_all [prover_sequent, gameB_model]
      -- by_cases na n ∈ Γ  --- Suspicious that we do not need this...
      -- case pos nφ_in => sorry -- easy
      -- case neg nφ_nin =>
    case neg_atom n =>
      intro con
      simp at con
      by_cases at n ∈ Γ  --- Suspicious that we do not need this...
      case pos nφ_in =>  -- easy
        let next_move : gamePos := ⟨Sum.inr (RuleApp.ax Γ n ⟨nφ_in, φ_in⟩), Γ :: Γs, Rs⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves ⟨Sum.inl Γ, Γs, Rs⟩ := by
          unfold next_move
          simp [coalgebraGame, Sequent.RuleApps]
          refine ⟨at n, nφ_in, by simp [φ_in]⟩
        have still_winning_next : winning strat next_move := by
          exact winning_of_whatever_other_move P_turn h ⟨next_move, next_in_moves⟩ -- removing by exact doesn't work ?
        have has_moves := winning_has_moves B_turn_next still_winning_next
        unfold Game.moves next_move at has_moves
        simp [coalgebraGame, RuleApp.Sequents] at has_moves
      case neg nφ_in =>
        simp [prover_sequent, gameB_model] at con
        exact nφ_in con
    case or φ1 φ2 => -- then we will make a move
      let next_move : gamePos := ⟨Sum.inr (RuleApp.or Γ φ1 φ2 φ_in), Γ :: Γs, Rs⟩
      have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
      have next_in_moves : next_move ∈ coalgebraGame.moves ⟨Sum.inl Γ, Γs, Rs⟩ := by
        unfold next_move
        simp [coalgebraGame, Sequent.RuleApps]
        refine ⟨φ1 v φ2, φ_in, by simp⟩
      have still_winning_next : winning strat next_move := by
        exact winning_of_whatever_other_move P_turn h ⟨next_move, next_in_moves⟩ -- removing by exact doesn't work ?
      have has_moves := winning_has_moves B_turn_next still_winning_next
      unfold Game.moves next_move at has_moves
      let next_next_move := strat next_move B_turn_next
        (by unfold next_move Game.Pos.moves Game.moves; exact has_moves)
      have still_winning_next_next : winning strat next_next_move := winning_of_winning_move B_turn_next still_winning_next
      rcases next_next_move_def : next_next_move with ⟨⟨info, Γs', Rs'⟩, in_moves⟩
      rcases info with Γ' | R'
      · have s_1 := gameB_model_sat strat (next_next_move_def ▸ still_winning_next_next) φ1 (by sorry)
        have s_2 := gameB_model_sat strat (next_next_move_def ▸ still_winning_next_next) φ2 (by sorry)
        have h : gen_submodel_around_form (gameB_model strat h) (gameB_model strat $ next_next_move_def ▸ still_winning_next_next) (φ1 v φ2) := by sorry
        have s_1 := @gen_submodel_preserves_not_eval _ _ _ _ (φ1 v φ2) h _ φ1 (by sorry) s_1
        have s_2 := @gen_submodel_preserves_not_eval _ _ _ _ (φ1 v φ2) h _ φ2 (by sorry) s_2
        simp
        constructor
        · convert s_1
          sorry
        · convert s_2
          sorry

        -- simp [Sequent.isValid] at this
        -- have ⟨α, M, u, u_prop⟩ := this
      · sorry -- contradiction
    case diamond =>
      sorry
    all_goals
      sorry
termination_by
  (WellFounded.transGen $ coalgebraGame.wf.2).wrap ⟨Sum.inl Γ, Γs, Rs⟩
decreasing_by
  all_goals
    apply @Relation.TransGen.tail _ _ _ next_move
    · apply Relation.TransGen.single
      apply coalgebraGame.move_rel
      simp only [WellFounded.wrap]
      grind
    · apply coalgebraGame.move_rel
      simp [WellFounded.wrap]
      grind

theorem gameB_general {Γ : Sequent} {Γs : List Sequent} {Rs : List RuleApp}
  (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Γ, Γs, Rs⟩)
  : ¬ ⊨ Γ := by
    have := gameB_model_sat strat h
    simp [Sequent.isValid]
    use gameB_model_type strat h
    use gameB_model strat h
    use ⟨⟨Sum.inl Γ, Γs, Rs⟩, by simp⟩

instance instModelUnit : Model Unit where
  V := fun _ _ ↦ True
  R := fun _ _ ↦ False
  trans := by intro _ _ _; simp
  con_wf := by
    apply WellFounded.intro
    intro u
    apply Acc.intro
    simp

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
