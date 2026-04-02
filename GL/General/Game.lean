import Pdl.Game
import GL.General.Proof

abbrev Builder := Player.A
abbrev Prover := Player.B

/-! ## The GL-proof game.

Builder-Prover game for constructive counter-models/proofs. Builder gets a rule application `R` and
plays an applicable sequent `Γ` in order to construct a counter-model. Prover get a sequent `Γ` and
plays rule applications `R` in order to construct a proof.
-/


/-- The available rule applications for a sequent `Γ`. -/
def Sequent.ruleApps (Γ : Sequent) : Finset RuleApp :=
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

/-- The sequents possible after a rule application `R`. -/
def RuleApp.sequents (R : RuleApp) : Finset Sequent := match R with
  | RuleApp.top _ _ => ∅
  | RuleApp.ax _ _ _ => ∅
  | RuleApp.and Δ φ ψ _ => {(Δ \ {φ & ψ}) ∪ {φ}, (Δ \ {φ & ψ}) ∪ {ψ}}
  | RuleApp.or Δ φ ψ _ => {(Δ \ {φ v ψ}) ∪ {φ, ψ}}
  | RuleApp.box Δ φ _ => {(Δ \ {□ φ}).D ∪ {φ}}

/-- Note: the game stores the history of which rule applications have come prior. -/
abbrev GamePos := (Sequent ⊕ RuleApp) × List Sequent × List RuleApp

inductive Move : GamePos → GamePos → Prop
  | prover  {R Rs Γ Γs} : R ∈ Γ.ruleApps → Move ⟨Sum.inl Γ, Γs, Rs⟩ ⟨Sum.inr R, Γ :: Γs, Rs⟩
  | builder {R Rs Γ Γs} : Γ ∈ R.sequents → Γ ∉ Γs → Move ⟨Sum.inr R, Γs, Rs⟩ ⟨Sum.inl Γ, Γs, R :: Rs⟩ -- no repeat sequents allowed!

/-- Given two consecutive Prover moves, the latter move is in the FL closure of the prior. -/
theorem move_move_in_FL {g1 g2 : GamePos} (h1 : (g1.1.isLeft)) (h3 : (g2.1.isLeft))
(g1_g2 : Relation.ReflTransGen (Relation.Comp Move Move) g1 g2): g2.1.getLeft h3 ∈ (g1.1.getLeft h1).FL.powerset := by
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
      have ih := Sequent.FL_mon ih
      simp [Sequent.FL_idem] at ih
      apply trans ?_ ih
      rcases R' <;> simp only [RuleApp.sequents, Finset.mem_singleton, Finset.notMem_empty, Finset.mem_insert] at Γ''_R'
      case or Δ φ ψ in_Δ =>
        subst Γ''_R'
        simp [Sequent.ruleApps] at R'_Γ
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
          simp [Sequent.ruleApps] at R'_Γ
          have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h
          simp only [h.1, Sequent.FL, Finset.subset_iff,
            Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton]
          intro χ χ_cases
          rcases χ_cases with h|h <;> subst_eqs
          · exact ⟨χ, h.1, Formula.FL_refl⟩
          · exact ⟨φ & ψ, in_Δ, by simp [Formula.FL, Formula.FL_refl]⟩
      case box Δ φ in_Δ =>
        subst Γ''_R'
        simp [Sequent.ruleApps] at R'_Γ
        have ⟨φ, φ_in, h⟩ := R'_Γ
        rcases φ <;> simp at h
        simp [Sequent.D, Finset.subset_iff, Sequent.FL, h.1]
        refine ⟨⟨_, h.1 ▸ φ_in, by simp [Formula.FL, h.2, Formula.FL_refl]⟩, ?_⟩
        intro χ χ_cases
        rcases χ_cases with h|h <;> subst_eqs
        · exact ⟨χ, h.1.1, Formula.FL_refl⟩
        · exact ⟨◇ χ, h, by simp [Formula.FL, Formula.FL_refl]⟩

/- This is the main helper for showing there is no infinite chain in the game, we do it 'from
   Prover's perspective' because that is where the FL properties are more readily available, but in
  fact it could be Builder's RuleApp `r` using `f r`. -/
lemma no_inf_chain_from_prover (g : ℕ → GamePos)
  (g_rel : ∀ (n : ℕ), Function.swap Move (g (n + 1)) (g n)) (h : (g 0).1.isLeft) : False := by
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

  have g0_gn : ∀ n, Relation.ReflTransGen Move (g 0) (g n) := by
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

/-- The game is converse well-founded. -/
lemma matches_finite : WellFounded (Function.swap Move) := by
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
  Pos := GamePos -- = (Sequent ⊕ RuleApp) × List Sequent × List RuleApp
  turn
    | ⟨Sum.inl _, _, _⟩ => Prover -- Prover gets a sequent and picks a rule application
    | ⟨Sum.inr _, _, _⟩ => Builder -- Builder gets a rule application and picks a sequent
  moves
    | ⟨Sum.inl Γ, Γs, Rs⟩ => Finset.map ⟨fun R ↦ ⟨Sum.inr R, Γ :: Γs, Rs⟩, by intro r1 r2; simp⟩ Γ.ruleApps
    | ⟨Sum.inr R, Γs, Rs⟩ => Finset.filterMap (fun Γ ↦ if Γ ∈ Γs then none else some ⟨Sum.inl Γ, Γs, R :: Rs⟩) R.sequents (by grind)
  wf := ⟨fun x y ↦ Move y x, matches_finite⟩
  move_rel := by
    intro ⟨info, Γs, Rs⟩ ⟨info', Γs', Rs'⟩ hyp
    rcases info with Γ | R
    · simp at hyp
      have ⟨R, R_prop, eq1, eq2, eq3⟩ := hyp
      subst_eqs
      simp
      exact Move.prover R_prop
    · simp at hyp
      have ⟨Γ, Γ_prop, nin, eq1, eq2, eq3⟩ := hyp
      subst_eqs
      simp
      exact Move.builder Γ_prop nin

/-- Move relation and being in the set of game moves are equivalant. -/
theorem move_iff_in_moves {g g' : coalgebraGame.Pos} : Move g g' ↔ g' ∈ coalgebraGame.moves g := by
  constructor
  · intro g_g'
    unfold Game.moves
    simp [coalgebraGame]
    cases g_g' <;> simp_all
  · intro in_moves
    exact @coalgebraGame.move_rel g g' in_moves

/-- We will always start the game from a sequent `Γ` and no history. -/
abbrev startPos (Γ : Sequent) : GamePos := ⟨Sum.inl Γ, [], []⟩
