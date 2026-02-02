import GL.Logic
import GL.SplitCoalgebraProof
import GL.Game
import GL.SplitCoalgebraGame
import GL.SplitCompleteness1
import GL.AxiomBlame

namespace Split
def after_box (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inl _, _, R :: _⟩ => R.isBox
  | _ => false

def is_box (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inr R, _, _⟩ => R.isBox
  | _ => false

def non_box_move : coalgebraGame.Pos → coalgebraGame.Pos → Prop :=
  fun x y ↦ move x y ∧ ¬ is_box y

-- structure where arguments are fields, upper case!
inductive maximal_path (Γ : SplitSequent) (strat : Strategy coalgebraGame Builder) : Type
| mp : (π : List coalgebraGame.Pos) → (ne : π ≠ []) → (chain : List.IsChain non_box_move π) →
       (max : ¬ ∃ z, non_box_move (π.getLast ne) z) → (head_cases : after_box (π.head ne) ∨ π.head ne = ⟨Sum.inl Γ, [], []⟩)
     → (in_cone : ∀ x ∈ π, inMyCone strat ⟨Sum.inl Γ, [], []⟩ x) → maximal_path Γ strat

@[simp]
def maximal_path.last {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} : maximal_path Γ strat → coalgebraGame.Pos
  | .mp π ne _ _ _ _ => π.getLast ne
@[simp]
def maximal_path.first {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} : maximal_path Γ strat → coalgebraGame.Pos
  | .mp π ne _ _ _ _ => π.head ne

@[simp]
def maximal_path.under {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} : maximal_path Γ strat → List coalgebraGame.Pos
  | .mp π _ _ _ _ _ => π

theorem maximal_path_starts_in_prover_turn {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
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

theorem maximal_path_ends_in_prover_turn {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
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


open Classical in
noncomputable
def make_path_from (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos) : List coalgebraGame.Pos :=
  match g_def : g with -- it thinks it is unused by it is used for termination
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', non_box_move g g'
    then ⟨Sum.inl Γ, Γs, Rs⟩ :: make_path_from strat exists_non_box_move.choose
    else [⟨Sum.inl Γ, Γs, Rs⟩] -- you idc about
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', non_box_move g g'
    then ⟨Sum.inr R, Γs, Rs⟩ :: make_path_from strat (strat ⟨Sum.inr R, Γs, Rs⟩
      (by simp [coalgebraGame]) ⟨exists_non_box_move.choose, move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)
    else [⟨Sum.inr R, Γs, Rs⟩] -- you must be cone
termination_by
  coalgebraGame.wf.2.wrap g
decreasing_by
· subst g_def
  apply coalgebraGame.move_rel
  simp [WellFounded.wrap]
  apply move_iff_in_moves.1
  exact exists_non_box_move.choose_spec.1
· subst g_def
  apply coalgebraGame.move_rel
  simp [WellFounded.wrap]

theorem make_path_from_is_nonempty (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : ¬ make_path_from strat g = ∅ := by
  unfold make_path_from
  simp [coalgebraGame, SplitSequent.RuleApps]
  split <;> split <;> simp

theorem make_path_from_head (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : (make_path_from strat g).head (make_path_from_is_nonempty strat g) = g := by
  unfold make_path_from
  simp [coalgebraGame, SplitSequent.RuleApps]
  split <;> split <;> simp

theorem make_path_from_head? (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : (make_path_from strat g).head? = some g := by
  unfold make_path_from
  simp [coalgebraGame, SplitSequent.RuleApps]
  split <;> split <;> simp

theorem make_path_from_is_chain (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : List.IsChain non_box_move (make_path_from strat g) :=
  open Classical in
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', non_box_move g g'
    then by
      simp_all [make_path_from]
      apply List.IsChain.cons
      · apply make_path_from_is_chain strat
      · simp
        intro g g_in
        have := make_path_from_head? strat (exists_non_box_move.choose)
        simp [this] at g_in
        subst g_in
        exact exists_non_box_move.choose_spec
    else by simp_all [make_path_from]
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', non_box_move g g'
    then by
      simp_all [make_path_from]
      apply List.IsChain.cons
      · apply make_path_from_is_chain strat
      · simp
        intro g g_in
        have in_moves := (strat (Sum.inr R, Γs, Rs) (by simp [coalgebraGame])
          ⟨exists_non_box_move.choose, move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩).2
        have := make_path_from_head? strat (strat (Sum.inr R, Γs, Rs) (by simp [coalgebraGame])
          ⟨exists_non_box_move.choose, move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)
        simp [this] at g_in
        simp [←g_in]
        constructor
        · exact move_iff_in_moves.2 in_moves
        · simp [Game.Pos.moves, coalgebraGame, -SetLike.coe_mem] at in_moves
          grind [is_box]
    else by simp_all [make_path_from]
termination_by
  coalgebraGame.wf.2.wrap g
decreasing_by
· subst g_def
  apply coalgebraGame.move_rel
  simp [WellFounded.wrap]
  apply move_iff_in_moves.1
  exact exists_non_box_move.choose_spec.1
· subst g_def
  apply coalgebraGame.move_rel
  simp [WellFounded.wrap]

theorem make_path_is_max (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : ¬ ∃ g', non_box_move ((make_path_from strat g).getLast (make_path_from_is_nonempty strat g)) g' :=
  open Classical in
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', non_box_move g g'
    then by
      simp_all only [make_path_from, ↓reduceDIte]
      convert make_path_is_max strat exists_non_box_move.choose using 4
      simp [List.getLast_cons (make_path_from_is_nonempty strat exists_non_box_move.choose)]
    else by simp_all [make_path_from]
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', non_box_move g g'
    then by
      simp_all only [make_path_from, ↓reduceDIte]
      convert make_path_is_max strat ((strat ⟨Sum.inr R, Γs, Rs⟩
      (by simp [coalgebraGame]) ⟨exists_non_box_move.choose, move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)) using 4
      simp [List.getLast_cons (make_path_from_is_nonempty strat ((strat ⟨Sum.inr R, Γs, Rs⟩
        (by simp [coalgebraGame]) ⟨exists_non_box_move.choose, move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)))]
    else by simp_all [make_path_from]
termination_by
  coalgebraGame.wf.2.wrap g
decreasing_by
· subst g_def
  apply coalgebraGame.move_rel
  simp [WellFounded.wrap]
  apply move_iff_in_moves.1
  exact exists_non_box_move.choose_spec.1
· subst g_def
  apply coalgebraGame.move_rel
  simp [WellFounded.wrap]

theorem make_path_is_in_cone (Δ : SplitSequent) (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos) (in_cone : inMyCone strat (Sum.inl Δ, [], []) g) (h : winning strat ⟨Sum.inl Δ, [], []⟩)
  : ∀ i, inMyCone strat (Sum.inl Δ, [], []) ((make_path_from strat g).get i) := by
  intro ⟨i_val, i_prop⟩
  cases i_val
  case zero =>
    convert in_cone using 1
    have := make_path_from_head strat g
    grind
  case succ i =>
    rcases g with ⟨Γ | R, Γs, Rs⟩
    · by_cases exists_non_box_move : ∃ g', non_box_move ⟨Sum.inl Γ, Γs, Rs⟩ g'
      · simp_all [make_path_from]
        simp [make_path_from] at i_prop
        apply make_path_is_in_cone Δ strat exists_non_box_move.choose ?_ h ⟨i, by grind⟩
        exact inMyCone.oStep in_cone (by simp [coalgebraGame]) (move_iff_in_moves.1 exists_non_box_move.choose_spec.1)
      · simp [make_path_from, exists_non_box_move] at i_prop
    · by_cases exists_non_box_move : ∃ g', non_box_move ⟨Sum.inr R, Γs, Rs⟩ g'
      · simp_all [make_path_from]
        simp [make_path_from, exists_non_box_move] at i_prop
        apply make_path_is_in_cone Δ strat _ ?_ h ⟨i, i_prop⟩
        apply inMyCone.myStep in_cone
      · simp [make_path_from, exists_non_box_move] at i_prop

theorem always_exists_maximal_path_from_root_or_after (Γ : SplitSequent) (strat : Strategy coalgebraGame Builder)
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) (g : coalgebraGame.Pos) (in_cone : inMyCone strat ⟨Sum.inl Γ, [], []⟩ g)
  (head_cases : after_box g ∨ g = ⟨Sum.inl Γ, [], []⟩) : ∃ π : maximal_path Γ strat, π.first = g := by
  refine ⟨maximal_path.mp ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · exact make_path_from strat g
  · exact make_path_from_is_nonempty strat g
  · exact make_path_from_is_chain strat g
  · exact make_path_is_max strat g
  · have := make_path_from_head strat g
    simp [this]
    exact head_cases
  · intro g' g'_in
    have ⟨i, i_eq⟩ := List.mem_iff_get.1 g'_in
    subst i_eq
    exact make_path_is_in_cone Γ strat g in_cone h i
  · exact make_path_from_head strat g

def prover_SplitSequent (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover) := match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => Γ
  | ⟨Sum.inr R, Γ :: Γs, Rs⟩ => False.elim (by simp [coalgebraGame] at h)

def first_SplitSequent {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
  : maximal_path Γ strat → SplitSequent := fun π ↦
  prover_SplitSequent π.first (maximal_path_starts_in_prover_turn π)

def last_SplitSequent {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  : maximal_path Γ strat → SplitSequent := fun π ↦
  prover_SplitSequent π.last (maximal_path_ends_in_prover_turn h π)

def path_relation (Γ : SplitSequent) (strat : Strategy coalgebraGame Builder) (π₁ π₂ : maximal_path Γ strat)
  := (Relation.Comp move move) π₁.last π₂.first

theorem Relation.TransGen.swap_eq_swap_rel {α : Type} (r : α → α → Prop) :
  Function.swap (Relation.TransGen r) = Relation.TransGen (Function.swap r) := by
  ext x y
  constructor
  all_goals
    intro mp
    simp [Function.swap] at mp
    induction mp
    case single x y_x => exact Relation.TransGen.single y_x
    case tail x z y_x x_z ih => exact Relation.TransGen.head x_z ih

theorem maximal_path_trans_gen
  (as) (ne : as ≠ []) (chain : List.IsChain non_box_move as) : Relation.ReflTransGen move (as.head ne) (as.getLast ne) := by
  induction chain
  case nil => simp at ne
  case singleton g =>
    simp
    exact Relation.ReflTransGen.refl
  case cons_cons g g' gs g_g' gs_chain ih =>
    simp at ih
    apply Relation.ReflTransGen.head g_g'.1 ih

def gameB_model (Γ : SplitSequent) {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  : Model (maximal_path Γ strat) where
  V π n := at n ∉ (last_SplitSequent h π).toSequent
  R := Relation.TransGen (path_relation Γ strat) -- maybe two steps of move
  trans := Relation.transitive_transGen
  con_wf := by
    simp [Relation.TransGen.swap_eq_swap_rel]
    apply WellFounded.transGen
    let F := Unit
    let instFunLike : FunLike F (maximal_path Γ strat) gamePos := by exact {
      coe := fun u π ↦ π.first
      coe_injective' := by intro u w; grind}
    have instRelHome : RelHomClass F (Function.swap (path_relation Γ strat)) (Relation.TransGen (Function.swap move)) := by exact {
      map_rel := by
        intro f ρ π π_ρ
        simp only [instFunLike]
        simp only [←Relation.TransGen.swap_eq_swap_rel, Function.swap]
        simp only [Function.swap, path_relation, Relation.Comp] at π_ρ
        rcases π_def : π with ⟨π_under, ne, chain⟩
        have π_rel := maximal_path_trans_gen π_under ne chain
        simp
        apply Relation.TransGen.trans_right π_rel
        have ⟨y, ⟨x_y, y_z⟩⟩ := π_ρ
        apply Relation.TransGen.tail (Relation.TransGen.single ?_) y_z
        · convert x_y
          simp [π_def]}
    have f : F := ()
    apply @RelHomClass.wellFounded _ _ (Function.swap (path_relation Γ strat)) (Relation.TransGen (Function.swap move)) F instFunLike instRelHome f (WellFounded.transGen coalgebraGame.wf.2)


theorem move_from_last_implies_box {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} (π : maximal_path Γ strat) :
  ∀ x, move π.last x → is_box x := by
  intro x π_x
  by_contra h
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  apply max
  refine ⟨x, ⟨π_x, h⟩⟩

theorem diamond_in_of_move_move_diamond_in {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  {x z} (hx hz) (x_z : (Relation.Comp move move) x z) :
    ∀ φ, ◇ φ ∈ (prover_SplitSequent x hx).toSequent → ◇ φ ∈ (prover_SplitSequent z hz).toSequent := by
  simp only [Relation.Comp] at x_z
  have ⟨y, x_y, y_z⟩ := x_z
  rcases x with ⟨Γ | R, Γs, Rs⟩ <;> simp only [coalgebraGame, reduceCtorEq] at hx
  rcases x_y
  case prover R R_Γ =>
  rcases y_z
  case builder Γ' Γ'_R nrep =>
  simp [prover_SplitSequent]
  intro φ φ_in
  simp [SplitSequent.RuleApps] at R_Γ
  rcases R_Γ with ⟨ψ, ψ_in, eq⟩ | ⟨ψ, ψ_in, eq⟩
  all_goals
    cases ψ <;> try grind [RuleApp.SplitSequents, SplitSequent.toSequent]
    case box =>
      simp at eq
      subst eq
      simp [RuleApp.SplitSequents] at Γ'_R
      subst Γ'_R
      simp [SplitSequent.D, SplitSequent.toSequent]
      right
      simp [SplitSequent.toSequent] at φ_in
      rcases φ_in with φ_in | φ_in <;> simp [SplitFormula.isDiamond, φ_in]

theorem diamond_in_last_of_diamond_in_first {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder} (h : winning strat ⟨Sum.inl Γ, [], []⟩) :
∀ π : maximal_path Γ strat, ∀ φ (i : ℕ) (lt : i < π.under.length) helper (ps),
  ◇ φ ∈ (prover_SplitSequent ((π.under)[π.under.length - i - 1]'helper) ps).toSequent → ◇ φ ∈ (last_SplitSequent h π).toSequent := by
  intro π φ i lt helper ps φ_in
  cases i
  case zero =>
    convert φ_in
    simp [last_SplitSequent, List.getLast_eq_getElem]
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
      have P_turn_u₂ : coalgebraGame.turn π[π.length - (i + 1 + 1) - 1 + 1 + 1] = Prover := by
        simp at ps
        rcases u₁_def : π[π.length - (i + 1 + 1) - 1 + 1] with ⟨Γ | R, Γs, Rs⟩
        · have := move_iff_in_moves.1 y_u₁.1
          exfalso
          rcases y_def : π[π.length - (i + 1 + 1) - 1] with ⟨Γ | R, Γs, Rs⟩
          · rw [u₁_def, y_def] at this
            simp [Game.moves, coalgebraGame] at this
          · simp [y_def] at ps
            simp [coalgebraGame] at ps
        · have := move_iff_in_moves.1 u₁_u₂.1
          rw [u₁_def] at this
          simp [Game.moves, coalgebraGame] at this
          have ⟨Γ, Γ_R, nrep, u₂_def⟩ := this
          apply congrArg coalgebraGame.turn at u₂_def
          exact Eq.symm u₂_def
      have := diamond_in_of_move_move_diamond_in h ps P_turn_u₂ ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in
      refine diamond_in_last_of_diamond_in_first h (maximal_path.mp π ne chain max head_cases in_cone) φ i (by grind) (by grind) ?_ ?_
      · simp
        convert P_turn_u₂ using 3
        grind
      · convert diamond_in_of_move_move_diamond_in h _ _ ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in using 3
        simp
        · grind
        · exact P_turn_u₂

theorem formula_in_successor_of_diamond_formula_in {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) {π ρ : maximal_path Γ strat} (π_ρ : path_relation Γ strat π ρ) :
  ∀ φ, ◇ φ ∈ (last_SplitSequent h π).toSequent → φ ∈ (first_SplitSequent ρ).toSequent := by
  intro φ diφ_in
  simp only [path_relation, Relation.Comp] at π_ρ
  have ⟨y, x_y, y_z⟩ := π_ρ
  have hx := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ | R, Γs, Rs⟩ <;> simp only [last_def, coalgebraGame, reduceCtorEq] at hx
  simp only [last_def] at x_y
  simp only [last_SplitSequent, last_def] at diφ_in
  simp [prover_SplitSequent] at diφ_in
  have := move_iff_in_moves.1 x_y
  simp only [coalgebraGame, Game.moves, Finset.mem_map, Function.Embedding.coeFn_mk] at this
  have ⟨R, R_Γ, y_def⟩ := this
  subst y_def
  have := move_iff_in_moves.1 y_z
  simp only [coalgebraGame, Game.moves, List.mem_cons, Finset.mem_filterMap,
    Option.ite_none_left_eq_some, not_or, Option.some.injEq] at this
  have ⟨Γ', Γ'_R, nrep, first_def⟩ := this
  simp only [first_SplitSequent, ←first_def]
  simp [prover_SplitSequent]
  simp [SplitSequent.RuleApps] at R_Γ
  rcases R_Γ with ⟨ψ, ψ_in, eq⟩ | ⟨ψ, ψ_in, eq⟩
  all_goals
    have R_box : R.isBox := by
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp at max
      have := max (Sum.inr R, Γ :: Γs, Rs)
      simp [non_box_move, is_box] at this
      apply this
      convert x_y
    cases ψ <;> try grind [RuleApp.isBox]
    case box =>
      simp at eq
      subst eq
      simp [RuleApp.SplitSequents] at Γ'_R
      subst Γ'_R
      simp [SplitSequent.D, SplitSequent.toSequent]
      simp [SplitSequent.toSequent] at diφ_in
      right
      rcases diφ_in with diφ_in | diφ_in <;> simp [diφ_in]


 theorem diamond_in_path_of_diamond_formula_in {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) {π ρ : maximal_path Γ strat} (π_ρ : Relation.TransGen (path_relation Γ strat) π ρ) :
  ∀ φ, ◇ φ ∈ (last_SplitSequent h π).toSequent → ◇ φ ∈ (first_SplitSequent ρ).toSequent := by
  intro φ φ_in
  induction π_ρ
  case single ρ π_ρ =>
    exact diamond_in_of_move_move_diamond_in h (maximal_path_ends_in_prover_turn h π) (maximal_path_starts_in_prover_turn ρ) π_ρ φ φ_in
  case tail γ _ _ rel ih =>
    apply diamond_in_of_move_move_diamond_in h (maximal_path_ends_in_prover_turn h _) (maximal_path_starts_in_prover_turn _) rel φ
    apply diamond_in_last_of_diamond_in_first h _ φ (γ.under.length - 1)
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert ih
      simp [first_SplitSequent]
      grind
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert (maximal_path_starts_in_prover_turn γ)
      rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind

theorem formula_in_path_of_diamond_formula_in {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat ⟨Sum.inl Γ, [], []⟩) {π ρ : maximal_path Γ strat} (π_ρ : Relation.TransGen (path_relation Γ strat) π ρ) :
  ∀ φ, ◇ φ ∈ (last_SplitSequent h π).toSequent → φ ∈ (first_SplitSequent ρ).toSequent := by
  intro φ φ_in
  cases π_ρ
  case single π_ρ => exact formula_in_successor_of_diamond_formula_in h π_ρ φ φ_in
  case tail γ π_γ γ_ρ =>
    have φ_in_γ := diamond_in_path_of_diamond_formula_in h π_γ φ φ_in
    apply formula_in_successor_of_diamond_formula_in h γ_ρ φ ?_
    apply diamond_in_last_of_diamond_in_first h γ φ (γ.under.length - 1)
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert φ_in_γ
      simp [first_SplitSequent]
      grind
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert (maximal_path_starts_in_prover_turn γ)
      rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind

set_option maxHeartbeats 1000000 in
theorem gameB_general_helper {Δ : SplitSequent} (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Δ, [], []⟩)
  (π : maximal_path Δ strat) (φ) (i : ℕ) (lt : i < π.under.length) helper (ps) :
  φ ∈ (prover_SplitSequent ((π.under)[π.under.length - i - 1]'helper) ps).toSequent → ¬Evaluate (gameB_model Δ h, π) φ := by
  simp [SplitSequent.toSequent]
  intro φ_in
  rcases φ_in with φ_in | φ_in
  · cases i
    case zero =>
      have φ_in' : Sum.inl φ ∈ last_SplitSequent h π := by
        convert φ_in
        simp [last_SplitSequent]
        congr
        grind
      have is_last : π.under[π.under.length - 0 - 1] = π.last := by simp; grind
      have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
      rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;> simp only [last_def, coalgebraGame, reduceCtorEq] at P_turn_y
      have eq : Γ' = last_SplitSequent h π := by
        unfold last_SplitSequent
        simp only [last_def]
        simp [prover_SplitSequent]
      subst eq
      have in_cone : inMyCone strat ⟨Sum.inl Δ, [], []⟩ π.last := by
        rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
        apply in_cone
        simp
      cases φ
      case bottom => simp_all
      case top =>
        let next_move : gamePos := ⟨Sum.inr (RuleApp.topₗ (last_SplitSequent h π) φ_in'), (last_SplitSequent h π) :: Γs', Rs'⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
          simp only [last_def]
          unfold next_move
          simp [coalgebraGame, SplitSequent.RuleApps]
          refine Or.inl ⟨⊤, φ_in', by simp⟩
        have still_winning_next : winning strat next_move :=
          in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
        have has_moves := winning_has_moves B_turn_next still_winning_next
        unfold Game.moves next_move at has_moves
        simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
      case atom n =>
        simp [gameB_model, SplitSequent.toSequent, -not_or]
        left
        convert φ_in
        simp [prover_SplitSequent, last_SplitSequent]
        grind
      case neg_atom n =>
        simp [gameB_model, SplitSequent.toSequent]
        constructor
        · intro nφ_in
          let next_move : gamePos := ⟨Sum.inr (RuleApp.axₗₗ (last_SplitSequent h π) n ⟨nφ_in, φ_in'⟩), (last_SplitSequent h π) :: Γs', Rs'⟩
          have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
          have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
            simp only [last_def]
            unfold next_move
            simp [coalgebraGame, SplitSequent.RuleApps]
            refine Or.inl ⟨at n, nφ_in, by simp [φ_in']⟩
          have still_winning_next : winning strat next_move :=
            in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
          have has_moves := winning_has_moves B_turn_next still_winning_next
          unfold Game.moves next_move at has_moves
          simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
        · intro nφ_in
          let next_move : gamePos := ⟨Sum.inr (RuleApp.axᵣₗ (last_SplitSequent h π) n ⟨nφ_in, φ_in'⟩), (last_SplitSequent h π) :: Γs', Rs'⟩
          have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
          have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
            simp only [last_def]
            unfold next_move
            simp [coalgebraGame, SplitSequent.RuleApps]
            refine Or.inr ⟨at n, nφ_in, by simp [φ_in']⟩
          have still_winning_next : winning strat next_move :=
            in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
          have has_moves := winning_has_moves B_turn_next still_winning_next
          unfold Game.moves next_move at has_moves
          simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
      case or φ1 φ2 => -- then we will make a move
        let next_move : gamePos := ⟨Sum.inr (RuleApp.orₗ (last_SplitSequent h π) φ1 φ2 φ_in'), (last_SplitSequent h π) :: Γs', Rs'⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
          simp only [last_def]
          unfold next_move
          simp [coalgebraGame, SplitSequent.RuleApps]
          exact Or.inl ⟨φ1 v φ2, φ_in', by simp⟩
        exfalso
        rcases π with ⟨π, ne, chain, max⟩
        apply max
        refine ⟨next_move, ?_, ?_⟩
        · exact move_iff_in_moves.2 next_in_moves
        · unfold next_move
          simp [is_box, RuleApp.isBox]
      case and φ1 φ2  => -- then we will make a move
        let next_move : gamePos := ⟨Sum.inr (RuleApp.andₗ (last_SplitSequent h π) φ1 φ2 φ_in'), (last_SplitSequent h π) :: Γs', Rs'⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
          simp only [last_def]
          unfold next_move
          simp [coalgebraGame, SplitSequent.RuleApps]
          exact Or.inl ⟨φ1 & φ2, φ_in', by simp⟩
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
        apply gameB_general_helper strat h ρ φ (ρ.under.length - 1) --- termination
        · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
          simp
          grind
        · have φ_in_2 : φ ∈ (first_SplitSequent ρ).toSequent := formula_in_path_of_diamond_formula_in h π_ρ φ (by simp [SplitSequent.toSequent, φ_in'])
          convert φ_in_2
          simp [first_SplitSequent]
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
        let next_move : coalgebraGame.Pos := ⟨Sum.inr (RuleApp.boxₗ (prover_SplitSequent π.last (is_last ▸ ps)) φ φ_in'), prover_SplitSequent π.last (is_last ▸ ps) :: π.last.2.1, π.last.2.2⟩
        have move_last_next : move π.last next_move := by
          unfold next_move
          simp only [last_def]
          apply move.prover
          simp [SplitSequent.RuleApps]
          refine Or.inl ⟨□ φ, φ_in', by simp [prover_SplitSequent]⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by simp [next_move, coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := move_iff_in_moves.1 move_last_next
        have next_in_cone : inMyCone strat (Sum.inl Δ, [], []) next_move :=
          inMyCone.oStep in_cone (by simp only [last_def, coalgebraGame, other_A_eq_B]) next_in_moves
        have B_turn_winning : winning strat next_move := in_cone_winning next_in_cone h
        let next_next_move := strat next_move B_turn_next (winning_has_moves B_turn_next B_turn_winning)
        have next_next_def := next_next_move.2
        simp only [next_move, Game.Pos.moves, coalgebraGame, RuleApp.SplitSequents, Finset.mem_filterMap, Finset.mem_singleton, ↓existsAndEq, List.mem_cons,
          Option.ite_none_left_eq_some, Option.some.injEq, true_and] at next_next_def
        have ⟨nrep, next_next_def⟩ := next_next_def
        have move_next_next : move next_move next_next_move.1 := move_iff_in_moves.2 next_next_move.2
        have next_next_in_cone : inMyCone strat (Sum.inl Δ, [], []) next_next_move.1 := by
          apply inMyCone.myStep next_in_cone
        have after_box_next_next : after_box next_next_move.1 := by
          rw [←next_next_def]
          simp [after_box, RuleApp.isBox]
        have ⟨ρ, ρ_def⟩ := always_exists_maximal_path_from_root_or_after Δ strat h next_next_move next_next_in_cone (Or.inl after_box_next_next)
        refine ⟨ρ, ?_, ?_⟩
        · simp [gameB_model]
          apply Relation.TransGen.single
          simp only [path_relation, Relation.Comp]
          exact ⟨next_move, move_last_next, ρ_def ▸ move_next_next⟩
        · apply gameB_general_helper strat h ρ φ (ρ.under.length - 1) --- termination
          · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
            simp
            grind
          · have φ_in_2 : φ ∈ (first_SplitSequent ρ).toSequent := by
              simp only [first_SplitSequent, ρ_def, ←next_next_def, SplitSequent.toSequent]
              simp [prover_SplitSequent]
            convert φ_in_2
            simp [first_SplitSequent]
            grind
          · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
            simp
            grind
          · convert (maximal_path_starts_in_prover_turn ρ)
            rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
            simp
            grind
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
        have P_turn : coalgebraGame.turn (maximal_path.mp π ne chain max head_cases in_cone).under[(maximal_path.mp π ne chain max head_cases in_cone).under.length - i - 1] = Prover := by
          convert P_turn_u₂
          convert Eq.symm u₂_def using 2
        simp [←eq] at u₂_def
        have eq_helper : prover_SplitSequent (maximal_path.mp π ne chain max head_cases in_cone).under[(maximal_path.mp π ne chain max head_cases in_cone).under.length - i - 1] P_turn = Γ' := by
          simp
          grind [prover_SplitSequent]
        by_cases Sum.inl φ ∈ Γ'
        case pos φ_in =>
          exact gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) φ i (by grind) (by grind) P_turn (by simp [SplitSequent.toSequent]; exact Or.inl (eq_helper ▸ φ_in))
        case neg nφ_in =>
          cases R <;> simp [RuleApp.SplitSequents] at Γ'_R
          case andₗ Δ ψ₁ ψ₂ in_Δ _ =>
            have ⟨eq1, eq2⟩ : φ = (ψ₁ & ψ₂) ∧ Γ = Δ := by
              rcases Γ'_R with eq | eq <;> subst eq
              all_goals
              simp [SplitSequent.RuleApps] at R_Γ
              rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
              simp [eq]
              by_contra ne
              apply nφ_in
              simp
              refine Or.inr ⟨?_, ne⟩
              convert φ_in
              simp [prover_SplitSequent, eq]
            subst eq1 eq2
            simp only [Evaluate, not_and_or]
            rcases Γ'_R with eq | eq <;> subst eq
            · left
              apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₁ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
            · right
              apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₂ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
          case andᵣ Δ ψ₁ ψ₂ in_Δ _ =>
            exfalso
            rcases Γ'_R with Γ'_R | Γ'_R <;> subst Γ'_R
            all_goals
            simp [prover_SplitSequent] at φ_in
            simp at nφ_in
            apply nφ_in
            simp [SplitSequent.RuleApps] at R_Γ
            rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
          case orₗ Δ ψ₁ ψ₂ in_Δ _ =>
            have ⟨eq1, eq2⟩ : φ = (ψ₁ v ψ₂) ∧ Γ = Δ := by
              subst Γ'_R
              simp [SplitSequent.RuleApps] at R_Γ
              rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
              all_goals
                simp [eq]
                by_contra ne
                apply nφ_in
                simp
                refine Or.inr (Or.inr ⟨?_, ne⟩)
                convert φ_in
                simp [prover_SplitSequent, eq]
            subst eq1 eq2 Γ'_R
            simp
            constructor
            · apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₁ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
            · apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₂ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
          case orᵣ Δ ψ₁ ψ₂ in_Δ _ =>
            exfalso
            subst Γ'_R
            simp [prover_SplitSequent] at φ_in
            simp at nφ_in
            apply nφ_in
            simp [SplitSequent.RuleApps] at R_Γ
            rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
          case boxₗ Δ ψ in_Δ _ => -- if this breaks in the future, then if u₁ is a box then we have a contradiction since u₁ sees u₂
            exfalso
            apply no_box_u₁
            have h : is_box ⟨Sum.inr (RuleApp.boxₗ Δ ψ in_Δ), Γ :: Γs, Rs⟩ := by simp [is_box, RuleApp.isBox]
            convert h
            exact Eq.symm u₁_def
          case boxᵣ Δ ψ in_Δ _ => --
            exfalso
            apply no_box_u₁
            have h : is_box ⟨Sum.inr (RuleApp.boxᵣ Δ ψ in_Δ), Γ :: Γs, Rs⟩ := by simp [is_box, RuleApp.isBox]
            convert h
            exact Eq.symm u₁_def
  · cases i
    case zero =>
      have φ_in' : Sum.inr φ ∈ last_SplitSequent h π := by
        convert φ_in
        simp [last_SplitSequent]
        congr
        grind
      have is_last : π.under[π.under.length - 0 - 1] = π.last := by simp; grind
      have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
      rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;> simp only [last_def, coalgebraGame, reduceCtorEq] at P_turn_y
      have eq : Γ' = last_SplitSequent h π := by
        unfold last_SplitSequent
        simp only [last_def]
        simp [prover_SplitSequent]
      subst eq
      have in_cone : inMyCone strat ⟨Sum.inl Δ, [], []⟩ π.last := by
        rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
        apply in_cone
        simp
      cases φ
      case bottom => simp_all
      case top =>
        let next_move : gamePos := ⟨Sum.inr (RuleApp.topᵣ (last_SplitSequent h π) φ_in'), (last_SplitSequent h π) :: Γs', Rs'⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
          simp only [last_def]
          unfold next_move
          simp [coalgebraGame, SplitSequent.RuleApps]
          refine Or.inr ⟨⊤, φ_in', by simp⟩
        have still_winning_next : winning strat next_move :=
          in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
        have has_moves := winning_has_moves B_turn_next still_winning_next
        unfold Game.moves next_move at has_moves
        simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
      case atom n =>
        simp [gameB_model, SplitSequent.toSequent, -not_or]
        right
        convert φ_in
        simp [prover_SplitSequent, last_SplitSequent]
        grind
      case neg_atom n =>
        simp [gameB_model, SplitSequent.toSequent]
        constructor
        · intro nφ_in
          by_cases φ_in'' : Sum.inl (na n) ∈ last_SplitSequent h π
          · let next_move : gamePos := ⟨Sum.inr (RuleApp.axₗₗ (last_SplitSequent h π) n ⟨nφ_in, φ_in''⟩), (last_SplitSequent h π) :: Γs', Rs'⟩
            have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
            have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
              simp only [last_def]
              unfold next_move
              simp [coalgebraGame, SplitSequent.RuleApps]
              refine Or.inl ⟨at n, nφ_in, by simp [φ_in'']⟩
            have still_winning_next : winning strat next_move :=
              in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
            have has_moves := winning_has_moves B_turn_next still_winning_next
            unfold Game.moves next_move at has_moves
            simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
          · let next_move : gamePos := ⟨Sum.inr (RuleApp.axₗᵣ (last_SplitSequent h π) n ⟨nφ_in, φ_in'⟩), (last_SplitSequent h π) :: Γs', Rs'⟩
            have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
            have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
              simp only [last_def]
              unfold next_move
              simp [coalgebraGame, SplitSequent.RuleApps]
              refine Or.inl ⟨at n, nφ_in, by simp [φ_in', φ_in'']⟩
            have still_winning_next : winning strat next_move :=
              in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
            have has_moves := winning_has_moves B_turn_next still_winning_next
            unfold Game.moves next_move at has_moves
            simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
        · intro nφ_in
          by_cases φ_in'' : Sum.inl (na n) ∈ last_SplitSequent h π
          · let next_move : gamePos := ⟨Sum.inr (RuleApp.axᵣₗ (last_SplitSequent h π) n ⟨nφ_in, φ_in''⟩), (last_SplitSequent h π) :: Γs', Rs'⟩
            have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
            have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
              simp only [last_def]
              unfold next_move
              simp [coalgebraGame, SplitSequent.RuleApps]
              refine Or.inr ⟨at n, nφ_in, by simp [φ_in', φ_in'']⟩
            have still_winning_next : winning strat next_move :=
              in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
            have has_moves := winning_has_moves B_turn_next still_winning_next
            unfold Game.moves next_move at has_moves
            simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
          · let next_move : gamePos := ⟨Sum.inr (RuleApp.axᵣᵣ (last_SplitSequent h π) n ⟨nφ_in, φ_in'⟩), (last_SplitSequent h π) :: Γs', Rs'⟩
            have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
            have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
              simp only [last_def]
              unfold next_move
              simp [coalgebraGame, SplitSequent.RuleApps]
              refine Or.inr ⟨at n, nφ_in, by simp [φ_in', φ_in'']⟩
            have still_winning_next : winning strat next_move :=
              in_cone_winning (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
            have has_moves := winning_has_moves B_turn_next still_winning_next
            unfold Game.moves next_move at has_moves
            simp [coalgebraGame, RuleApp.SplitSequents] at has_moves
      case or φ1 φ2 => -- then we will make a move
        let next_move : gamePos := ⟨Sum.inr (RuleApp.orᵣ (last_SplitSequent h π) φ1 φ2 φ_in'), (last_SplitSequent h π) :: Γs', Rs'⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
          simp only [last_def]
          unfold next_move
          simp [coalgebraGame, SplitSequent.RuleApps]
          exact Or.inr ⟨φ1 v φ2, φ_in', by simp⟩
        exfalso
        rcases π with ⟨π, ne, chain, max⟩
        apply max
        refine ⟨next_move, ?_, ?_⟩
        · exact move_iff_in_moves.2 next_in_moves
        · unfold next_move
          simp [is_box, RuleApp.isBox]
      case and φ1 φ2  => -- then we will make a move
        let next_move : gamePos := ⟨Sum.inr (RuleApp.andᵣ (last_SplitSequent h π) φ1 φ2 φ_in'), (last_SplitSequent h π) :: Γs', Rs'⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by unfold Game.turn next_move; simp [coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
          simp only [last_def]
          unfold next_move
          simp [coalgebraGame, SplitSequent.RuleApps]
          exact Or.inr ⟨φ1 & φ2, φ_in', by simp⟩
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
        apply gameB_general_helper strat h ρ φ (ρ.under.length - 1) --- termination
        · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
          simp
          grind
        · have φ_in_2 : φ ∈ (first_SplitSequent ρ).toSequent := formula_in_path_of_diamond_formula_in h π_ρ φ (by simp [SplitSequent.toSequent, φ_in'])
          convert φ_in_2
          simp [first_SplitSequent]
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
        let next_move : coalgebraGame.Pos := ⟨Sum.inr (RuleApp.boxᵣ (prover_SplitSequent π.last (is_last ▸ ps)) φ φ_in'), prover_SplitSequent π.last (is_last ▸ ps) :: π.last.2.1, π.last.2.2⟩
        have move_last_next : move π.last next_move := by
          unfold next_move
          simp only [last_def]
          apply move.prover
          simp [SplitSequent.RuleApps]
          refine Or.inr ⟨□ φ, φ_in', by simp [prover_SplitSequent]⟩
        have B_turn_next : coalgebraGame.turn next_move = Builder := by simp [next_move, coalgebraGame]
        have next_in_moves : next_move ∈ coalgebraGame.moves π.last := move_iff_in_moves.1 move_last_next
        have next_in_cone : inMyCone strat (Sum.inl Δ, [], []) next_move :=
          inMyCone.oStep in_cone (by simp only [last_def, coalgebraGame, other_A_eq_B]) next_in_moves
        have B_turn_winning : winning strat next_move := in_cone_winning next_in_cone h
        let next_next_move := strat next_move B_turn_next (winning_has_moves B_turn_next B_turn_winning)
        have next_next_def := next_next_move.2
        simp only [next_move, Game.Pos.moves, coalgebraGame, RuleApp.SplitSequents, Finset.mem_filterMap, Finset.mem_singleton, ↓existsAndEq, List.mem_cons,
          Option.ite_none_left_eq_some, Option.some.injEq, true_and] at next_next_def
        have ⟨nrep, next_next_def⟩ := next_next_def
        have move_next_next : move next_move next_next_move.1 := move_iff_in_moves.2 next_next_move.2
        have next_next_in_cone : inMyCone strat (Sum.inl Δ, [], []) next_next_move.1 := by
          apply inMyCone.myStep next_in_cone
        have after_box_next_next : after_box next_next_move.1 := by
          rw [←next_next_def]
          simp [after_box, RuleApp.isBox]
        have ⟨ρ, ρ_def⟩ := always_exists_maximal_path_from_root_or_after Δ strat h next_next_move next_next_in_cone (Or.inl after_box_next_next)
        refine ⟨ρ, ?_, ?_⟩
        · simp [gameB_model]
          apply Relation.TransGen.single
          simp only [path_relation, Relation.Comp]
          exact ⟨next_move, move_last_next, ρ_def ▸ move_next_next⟩
        · apply gameB_general_helper strat h ρ φ (ρ.under.length - 1) --- termination
          · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
            simp
            grind
          · have φ_in_2 : φ ∈ (first_SplitSequent ρ).toSequent := by
              simp only [first_SplitSequent, ρ_def, ←next_next_def, SplitSequent.toSequent]
              simp [prover_SplitSequent]
            convert φ_in_2
            simp [first_SplitSequent]
            grind
          · rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
            simp
            grind
          · convert (maximal_path_starts_in_prover_turn ρ)
            rcases ρ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
            simp
            grind
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
        have P_turn : coalgebraGame.turn (maximal_path.mp π ne chain max head_cases in_cone).under[(maximal_path.mp π ne chain max head_cases in_cone).under.length - i - 1] = Prover := by
          convert P_turn_u₂
          convert Eq.symm u₂_def using 2
        simp [←eq] at u₂_def
        have eq_helper : prover_SplitSequent (maximal_path.mp π ne chain max head_cases in_cone).under[(maximal_path.mp π ne chain max head_cases in_cone).under.length - i - 1] P_turn = Γ' := by
          simp
          grind [prover_SplitSequent]
        by_cases Sum.inr φ ∈ Γ'
        case pos φ_in =>
          exact gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) φ i (by grind) (by grind) P_turn (by simp [SplitSequent.toSequent]; exact Or.inr (eq_helper ▸ φ_in))
        case neg nφ_in =>
          cases R <;> simp [RuleApp.SplitSequents] at Γ'_R
          case andᵣ Δ ψ₁ ψ₂ in_Δ _ =>
            have ⟨eq1, eq2⟩ : φ = (ψ₁ & ψ₂) ∧ Γ = Δ := by
              rcases Γ'_R with eq | eq <;> subst eq
              all_goals
              simp [SplitSequent.RuleApps] at R_Γ
              rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
              simp [eq]
              by_contra ne
              apply nφ_in
              simp
              refine Or.inr ⟨?_, ne⟩
              convert φ_in
              simp [prover_SplitSequent, eq]
            subst eq1 eq2
            simp only [Evaluate, not_and_or]
            rcases Γ'_R with eq | eq <;> subst eq
            · left
              apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₁ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
            · right
              apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₂ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
          case andₗ Δ ψ₁ ψ₂ in_Δ _ =>
            exfalso
            rcases Γ'_R with Γ'_R | Γ'_R <;> subst Γ'_R
            all_goals
            simp [prover_SplitSequent] at φ_in
            simp at nφ_in
            apply nφ_in
            simp [SplitSequent.RuleApps] at R_Γ
            rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
          case orᵣ Δ ψ₁ ψ₂ in_Δ _ =>
            have ⟨eq1, eq2⟩ : φ = (ψ₁ v ψ₂) ∧ Γ = Δ := by
              subst Γ'_R
              simp [SplitSequent.RuleApps] at R_Γ
              rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
              all_goals
                simp [eq]
                by_contra ne
                apply nφ_in
                simp
                refine Or.inr (Or.inr ⟨?_, ne⟩)
                convert φ_in
                simp [prover_SplitSequent, eq]
            subst eq1 eq2 Γ'_R
            simp
            constructor
            · apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₁ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
            · apply gameB_general_helper strat h (maximal_path.mp π ne chain max head_cases in_cone) ψ₂ i (by grind) (by grind) P_turn
              rw [eq_helper]
              simp [SplitSequent.toSequent]
          case orₗ Δ ψ₁ ψ₂ in_Δ _ =>
            exfalso
            subst Γ'_R
            simp [prover_SplitSequent] at φ_in
            simp at nφ_in
            apply nφ_in
            simp [SplitSequent.RuleApps] at R_Γ
            rcases R_Γ with ⟨χ, χ_in, eq⟩ | ⟨χ, χ_in, eq⟩ <;> cases χ <;> simp at eq <;> try grind
          case boxₗ Δ ψ in_Δ _ => -- if this breaks in the future, then if u₁ is a box then we have a contradiction since u₁ sees u₂
            exfalso
            apply no_box_u₁
            have h : is_box ⟨Sum.inr (RuleApp.boxₗ Δ ψ in_Δ), Γ :: Γs, Rs⟩ := by simp [is_box, RuleApp.isBox]
            convert h
            exact Eq.symm u₁_def
          case boxᵣ Δ ψ in_Δ _ =>
            exfalso
            apply no_box_u₁
            have h : is_box ⟨Sum.inr (RuleApp.boxᵣ Δ ψ in_Δ), Γ :: Γs, Rs⟩ := by simp [is_box, RuleApp.isBox]
            convert h
            exact Eq.symm u₁_def
termination_by (φ.size, i)
decreasing_by
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
  · subst_eqs
    apply Prod.Lex.right
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
  · subst_eqs
    apply Prod.Lex.right
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega
  · subst_eqs
    apply Prod.Lex.left
    simp [Formula.size]
    omega

theorem gameB_general {Γ : SplitSequent}
  (strat : Strategy coalgebraGame Builder) (h : winning strat ⟨Sum.inl Γ, [], []⟩)
  : ¬ (⊨ Γ) := by
    simp [SplitSequent.isValid]
    use maximal_path Γ strat
    use gameB_model Γ h
    have ⟨π, π_head_eq⟩ := always_exists_maximal_path_from_root_or_after Γ strat h ⟨Sum.inl Γ, [], []⟩ inMyCone.nil (Or.inr rfl)
    use π
    constructor
    all_goals
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
        simp [prover_SplitSequent, SplitSequent.toSequent, φ_in]

def startPos (Γ : SplitSequent) : gamePos := ⟨Sum.inl Γ, [], []⟩

theorem Completeness (Γ : SplitSequent) : ⊨ Γ → ⊢ Γ := by
  intro Γ_sat
  rcases gamedet coalgebraGame (startPos Γ) with builder_wins | prover_wins
  · have ⟨strat, h⟩ := builder_wins
    have nΓ_sat := gameB_general strat h
    exfalso
    exact nΓ_sat Γ_sat
  · have ⟨strat, h⟩ := prover_wins
    exact gameP_general strat h

#axiom_blame Completeness
