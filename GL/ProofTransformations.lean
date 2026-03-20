import GL.Logic
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs
import GL.SplitCutCoalgebraProof

namespace CutPre

inductive RuleApp {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent)
  | pre : (y : 𝕏.X) → (y ∈ Split.p 𝕏.α x) → RuleApp x τ
  | cutₗ : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ
  | cutᵣ : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ
  | wkₗ : (Δ : SplitSequent) → (A : Formula) → (Sum.inl A) ∈ Δ → RuleApp x τ
  | wkᵣ : (Δ : SplitSequent) → (A : Formula) → (Sum.inr A) ∈ Δ → RuleApp x τ
  | topₗ : (Δ : SplitSequent) → (Sum.inl ⊤) ∈ Δ → RuleApp x τ
  | topᵣ : (Δ : SplitSequent) → (Sum.inr ⊤) ∈ Δ → RuleApp x τ
  | axₗₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp x τ
  | axₗᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp x τ
  | axᵣₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp x τ
  | axᵣᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp x τ
  | andₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A & B) ∈ Δ → RuleApp x τ
  | andᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A & B) ∈ Δ → RuleApp x τ
  | orₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A v B) ∈ Δ → RuleApp x τ
  | orᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A v B) ∈ Δ → RuleApp x τ
  | boxₗ : (Δ : SplitSequent) → (A : Formula) → Sum.inl (□ A) ∈ Δ → RuleApp x τ
  | boxᵣ : (Δ : SplitSequent) → (A : Formula) → Sum.inr (□ A) ∈ Δ → RuleApp x τ

def fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent
  | RuleApp.pre _ _ => ∅
  | RuleApp.cutₗ _ _ => ∅
  | RuleApp.cutᵣ _ _ => ∅
  | RuleApp.wkₗ _ A _ => {Sum.inl A}
  | RuleApp.wkᵣ _ A _ => {Sum.inr A}
  | RuleApp.topₗ _ _ => {Sum.inl ⊤}
  | RuleApp.topᵣ _ _ => {Sum.inr ⊤}
  | RuleApp.axₗₗ _ n _ => {Sum.inl $ at n, Sum.inl $ na n}
  | RuleApp.axₗᵣ _ n _ => {Sum.inl $ at n, Sum.inr $ na n}
  | RuleApp.axᵣₗ _ n _ => {Sum.inr $ at n, Sum.inl $ na n}
  | RuleApp.axᵣᵣ _ n _ => {Sum.inr $ at n, Sum.inr $ na n}
  | RuleApp.andₗ _ A B _ => {Sum.inl (A & B)}
  | RuleApp.andᵣ _ A B _ => {Sum.inr (A & B)}
  | RuleApp.orₗ _ A B _ => {Sum.inl (A v B)}
  | RuleApp.orᵣ _ A B _ => {Sum.inr (A v B)}
  | RuleApp.boxₗ _ A _ => {Sum.inl (□ A)}
  | RuleApp.boxᵣ _ A _ => {Sum.inr (□ A)}

def f {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent
  | RuleApp.pre y _ => τ y
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ _ _ => Δ
  | RuleApp.wkᵣ Δ _ _ => Δ
  | RuleApp.topₗ Δ _ => Δ
  | RuleApp.topᵣ Δ _ => Δ
  | RuleApp.axₗₗ Δ _ _ => Δ
  | RuleApp.axₗᵣ Δ _ _ => Δ
  | RuleApp.axᵣₗ Δ _ _ => Δ
  | RuleApp.axᵣᵣ Δ _ _ => Δ
  | RuleApp.andₗ Δ _ _ _ => Δ
  | RuleApp.andᵣ Δ _ _ _ => Δ
  | RuleApp.orₗ Δ _ _ _ => Δ
  | RuleApp.orᵣ Δ _ _ _ => Δ
  | RuleApp.boxₗ Δ _ _ => Δ
  | RuleApp.boxᵣ Δ _ _ => Δ

def fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent := fun r ↦ f r \ fₚ r

theorem fₙ_alternate {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (r : RuleApp x τ) : fₙ r = match r with
  | RuleApp.pre y _ => τ y
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ A _ =>  Δ \ {Sum.inl A}
  | RuleApp.wkᵣ Δ A _ =>  Δ \ {Sum.inr A}
  | RuleApp.topₗ Δ _ => Δ \ {Sum.inl ⊤}
  | RuleApp.topᵣ Δ _ => Δ \ {Sum.inr ⊤}
  | RuleApp.axₗₗ Δ n _ => Δ \ {Sum.inl $ at n, Sum.inl $ na n}
  | RuleApp.axₗᵣ Δ n _ => Δ \ {Sum.inl $ at n, Sum.inr $ na n}
  | RuleApp.axᵣₗ Δ n _ => Δ \ {Sum.inr $ at n, Sum.inl $ na n}
  | RuleApp.axᵣᵣ Δ n _ => Δ \ {Sum.inr $ at n, Sum.inr $ na n}
  | RuleApp.andₗ Δ A B _ => Δ \ {Sum.inl (A & B)}
  | RuleApp.andᵣ Δ A B _ => Δ \ {Sum.inr (A & B)}
  | RuleApp.orₗ Δ A B _ => Δ \ {Sum.inl (A v B)}
  | RuleApp.orᵣ Δ A B _ => Δ \ {Sum.inr (A v B)}
  | RuleApp.boxₗ Δ A _ => Δ \ {Sum.inl (□ A)}
  | RuleApp.boxᵣ Δ A _ => Δ \ {Sum.inr (□ A)} := by cases r <;> simp [fₙ, f, fₚ]

universe u
@[simp] def T {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨λ X ↦ ((RuleApp x τ × List X) : Type u), by rintro X Y f ⟨r, A⟩; exact ⟨r, A.map f⟩, by aesop_cat, by aesop_cat⟩

def r {X : Type u} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (α : X → (T x τ).obj X) (x : X) := (α x).1
def p {X : Type u} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (α : X → (T x τ).obj X) (x : X) := (α x).2
def edge  {X : Type u} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (α : X → (T x τ).obj X) (x y : X) : Prop := y ∈ p α x

def RuleApp.isBox {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : RuleApp x τ → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

def RuleApp.isNonAxLeaf {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : RuleApp x τ → Prop
  | RuleApp.pre _ _ => true
  | _ => false


/-

~Eₓ | f^r(x)    ~ιₓ | ~Eₓ
------------------------cutₗ
      ~ιₓ | f^r(x)

-/
structure CutProofFromPremises {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) where
  X : Type
  α : X → (T x τ).obj X
  root : X
  step : ∀ (x : X), match r α x with
    | RuleApp.pre _ _ => p α x = []
    | RuleApp.cutₗ _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).filterRight ∪ {Sum.inl $ A}, (fₙ (r α x)).filterLeft ∪ {Sum.inr $ ~A}]
    | RuleApp.cutᵣ _ A => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).filterLeft ∪ {Sum.inr $ A}, (fₙ (r α x)).filterRight ∪ {Sum.inl $ ~A}]
    | RuleApp.wkₗ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.wkᵣ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.topₗ _ _ => p α x = ∅
    | RuleApp.topᵣ _ _ => p α x = ∅
    | RuleApp.axₗₗ _ _ _ => p α x = ∅
    | RuleApp.axₗᵣ _ _ _ => p α x = ∅
    | RuleApp.axᵣₗ _ _ _ => p α x = ∅
    | RuleApp.axᵣᵣ _ _ _ => p α x = ∅
    | RuleApp.andₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ => (p α x).map (λ x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inr A}]
  path : ∀ x, ∀ f : {f : ℕ → X // f 0 = x ∧ ∀ (n : ℕ), edge α (f n) (f (n + 1))},
    ∀ n, ∃ m, (r α (f.1 (n + m))).isBox

-- def CutProofFromPremises.Proves {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} (𝕐 : CutProofFromPremises x τ) (Δ : SplitSequent) : Prop := ∃ x : 𝕐.X, f (r 𝕐.α x) = Δ
-- infixr:6 "⊢" => CutProofFromPremises.Proves

end CutPre

namespace Split

def CutPre.Proves {𝕏 : Proof} (x : 𝕏.X) {σ} (𝕐 : CutPre.CutProofFromPremises x σ) (Δ : SplitSequent) : Prop :=
  CutPre.f (CutPre.r 𝕐.α 𝕐.root) = Δ

def ProofTranslationMap {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) : (y : 𝕏.X) × (PartialProof y).X → SplitCut.T.obj ((y : 𝕏.X) × (PartialProof y).X) :=
  fun ⟨y, z_y⟩ ↦
  match (@CutPre.r _ _ _ _ (PartialProof y).α z_y) with
  | .pre z _ => ⟨SplitCut.RuleApp.skp (σ z), [⟨z, (PartialProof z).root⟩]⟩ -- map to the root
  | .cutₗ Δ A => ⟨SplitCut.RuleApp.cutₗ Δ A, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .cutᵣ Δ A => ⟨SplitCut.RuleApp.cutᵣ Δ A, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .wkₗ Δ A in_Δ => ⟨SplitCut.RuleApp.wkₗ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .wkᵣ Δ A in_Δ => ⟨SplitCut.RuleApp.wkᵣ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .topₗ Δ in_Δ => ⟨SplitCut.RuleApp.topₗ Δ in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .topᵣ Δ in_Δ => ⟨SplitCut.RuleApp.topᵣ Δ in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axₗₗ Δ n in_Δ => ⟨SplitCut.RuleApp.axₗₗ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axₗᵣ Δ n in_Δ => ⟨SplitCut.RuleApp.axₗᵣ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axᵣₗ Δ n in_Δ => ⟨SplitCut.RuleApp.axᵣₗ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .axᵣᵣ Δ n in_Δ => ⟨SplitCut.RuleApp.axᵣᵣ Δ n in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .andₗ Δ A B in_Δ => ⟨SplitCut.RuleApp.andₗ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .andᵣ Δ A B in_Δ => ⟨SplitCut.RuleApp.andᵣ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .orₗ Δ A B in_Δ => ⟨SplitCut.RuleApp.orₗ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .orᵣ Δ A B in_Δ => ⟨SplitCut.RuleApp.orᵣ Δ A B in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .boxₗ Δ A in_Δ => ⟨SplitCut.RuleApp.boxₗ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩
  | .boxᵣ Δ A in_Δ => ⟨SplitCut.RuleApp.boxᵣ Δ A in_Δ, (CutPre.p (PartialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)⟩

@[simp]
theorem ProofTranslation_f {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  SplitCut.f (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩) = CutPre.f (@CutPre.r _ _ _ _ (PartialProof y).α z_in_Cy) := by
    cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.f, CutPre.f]

@[simp]
theorem ProofTranslation_fₚ {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  SplitCut.fₚ (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩) = CutPre.fₚ (@CutPre.r _ _ _ _ (PartialProof y).α z_in_Cy) := by
    cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.fₚ, CutPre.fₚ]

@[simp]
theorem ProofTranslation_fₙ {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (y : 𝕏.X) (z_in_Cy : (PartialProof y).X) :
  SplitCut.fₙ (SplitCut.r (ProofTranslationMap PartialProof) ⟨y, z_in_Cy⟩) = CutPre.fₙ (@CutPre.r _ _ _ _ (PartialProof y).α z_in_Cy) := by
    cases r_def : (CutPre.r (PartialProof y).α z_in_Cy) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.fₙ_alternate, CutPre.fₙ_alternate]

theorem ProofTranslation_isBox {𝕏 : Proof} {σ} (PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ) (z_in_Cy : (y : 𝕏.X) × (PartialProof y).X) :
  (SplitCut.r (ProofTranslationMap PartialProof) z_in_Cy).isBox ↔ (CutPre.r (PartialProof z_in_Cy.1).α z_in_Cy.2).isBox := by
  cases r_def : (CutPre.r (PartialProof z_in_Cy.1).α z_in_Cy.2) <;> simp_all [SplitCut.r, ProofTranslationMap, SplitCut.RuleApp.isBox, CutPre.RuleApp.isBox]

open Classical in
noncomputable def dep_sum_seq_proj {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  : ℕ → α × ℕ
  | 0 => ⟨(f (Nat.find (h 0) + 1)).1, Nat.find (h 0) + 1⟩
  | n + 1 => by
      have ih := dep_sum_seq_proj h n
      exact ⟨(f (Nat.find (h ih.2) + 1)).1, Nat.find (h ih.2) + 1⟩

theorem infinite_dep_sum_sequence_proj_eq {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2)) :
  ∀ n, (f (dep_sum_seq_proj h n).2).1 = (dep_sum_seq_proj h n).1 := by
  intro n
  cases n <;> simp [dep_sum_seq_proj] -- surprised how this works?

theorem dep_sum_seq_proj_leq {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a} {Q : (a : α) → β a → β a → Prop} (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2)) :
  ∀ n, n ≤ (dep_sum_seq_proj h n).2 := by
  intro n
  induction n
  case zero => simp
  case succ n ih =>
    simp [dep_sum_seq_proj]
    grind

open Classical in
theorem fst_same_in_range {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2)) :
  ∀ n, ∀ m, n ≤ Nat.find (h (dep_sum_seq_proj h m).2) → n ≥ (dep_sum_seq_proj h m).2 → (f (dep_sum_seq_proj h m).2).1 = (f n).1 := by
  intro n m n_lt n_ge
  have n_le_m := dep_sum_seq_proj_leq h n
  induction n
  case zero =>
    simp at n_ge
    simp [n_ge]
  case succ n ih =>
    have neq := Nat.find_spec (h (n + 1))
    by_cases eq : n + 1 = (dep_sum_seq_proj h m).2
    case pos => simp [eq]
    case neg =>
      have := ih (by grind) (by grind) (dep_sum_seq_proj_leq h n)
      simp [this]
      by_contra eq
      have : ∀ h : (f n).1 = (f (n + 1)).1, ¬ Q (f n).1 (f n).2 (h ▸ (f (n + 1)).2) := by
        intro h
        exfalso
        exact eq h
      have := @Nat.find_le _ _ _ (h n) ⟨by grind, this⟩
      have : Nat.find (h (dep_sum_seq_proj h m).2) ≤ Nat.find (h n) := by
        have g : ∀ n, ∀ m, n ≤ m → Nat.find (h n) ≤ Nat.find (h m) :=
          fun n m n_lt_m ↦ @Nat.find_le _ _ _ (h n) ⟨by grind, (Nat.find_spec (h m)).2⟩
        apply g
        grind
      linarith

open Classical in
theorem infinite_dep_sum_chain
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {R : α → α → Prop}  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  (f_chain : ∀ n, Sigma.Lex R Q (f n) (f (n + 1))) :
  ∀ n, R (dep_sum_seq_proj h n).1 (dep_sum_seq_proj h (n + 1)).1 := by
  intro n
  simp [←infinite_dep_sum_sequence_proj_eq]
  simp [dep_sum_seq_proj]
  have n_le_m := dep_sum_seq_proj_leq h n
  have h1 := fst_same_in_range h (Nat.find (h (dep_sum_seq_proj h n).2)) n (by simp) (by grind)
  rw [h1]
  rcases Sigma.lex_iff.1 (f_chain (Nat.find (h (dep_sum_seq_proj h n).2))) with R_rel | ⟨eq, Q_rel⟩
  · exact R_rel
  · exfalso
    apply (Nat.find_spec (h (dep_sum_seq_proj h n).2)).2 eq
    convert Q_rel <;> simp


open Classical in
noncomputable def infinite_dep_sum_chain_finite_subchain
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  -- (p : α → Prop) (q : (a : α) × β a → Prop)
  -- (inf : ∀ n, ∃ m, p (dep_sum_seq_proj h (n + m)).1)
  (m : ℕ) : Fin ((Nat.find (h (dep_sum_seq_proj h m).2) - (dep_sum_seq_proj h m).2) + 1) → β (dep_sum_seq_proj h m).1 :=
    fun ⟨n, n_prop⟩ ↦
    have eq : (f ((dep_sum_seq_proj h m).2 + n)).fst = (dep_sum_seq_proj h m).1 := by
      rw [←infinite_dep_sum_sequence_proj_eq h m]
      apply Eq.symm $ fst_same_in_range h ((dep_sum_seq_proj h m).2 + n) m ?_ ?_ <;> grind
    eq ▸ (f ((dep_sum_seq_proj h m).2 + n)).2

open Classical in
theorem infinite_dep_sum_chain_finite_subchain_prop
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  -- (p : α → Prop) (q : (a : α) × β a → Prop)
  -- (inf : ∀ n, ∃ m, p (dep_sum_seq_proj h (n + m)).1)
  (m : ℕ) :
    ∀ k : Fin (Nat.find (h (dep_sum_seq_proj h m).2) - (dep_sum_seq_proj h m).2),
    Q (dep_sum_seq_proj h m).1 (infinite_dep_sum_chain_finite_subchain h m k.castSucc) (infinite_dep_sum_chain_finite_subchain h m k.succ) := by
    intro ⟨k, k_prop⟩
    unfold infinite_dep_sum_chain_finite_subchain
    simp
    have := @Nat.find_min _ _ (h (dep_sum_seq_proj h m).2) ((dep_sum_seq_proj h m).2 + k) (by grind)
    simp at this
    convert this.2 using 1
    · rw [←infinite_dep_sum_sequence_proj_eq]
      apply fst_same_in_range h ((dep_sum_seq_proj h m).2 + k) m ?_ ?_ <;> grind
    · simp
    · grind

theorem infinite_dep_sum_chain_inf
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  (p : α → Prop) (q : (a : α) × β a → Prop)
  (inf : ∀ n, ∃ m, p (dep_sum_seq_proj h (n + m)).1)
  (conv : ∀ n, p (dep_sum_seq_proj h n).1 → ∃ m, q (f ((dep_sum_seq_proj h n).2 + m)))
  : ∀ n, ∃ m, q (f (n + m))
  := by
  intro n
  have ⟨m, m_prop⟩ := inf n
  have ⟨l, l_prop⟩ := conv (n + m) m_prop
  use (dep_sum_seq_proj h (n + m)).2 - n + l
  convert l_prop using 2
  have := dep_sum_seq_proj_leq h (n + m)
  omega

open Classical in
set_option maxHeartbeats 10000000 in
noncomputable def ProofTranslation {𝕏 : Proof} {σ}
(PartialProof : (x : 𝕏.X) → CutPre.CutProofFromPremises x σ)
(root_proves : ∀ x, CutPre.Proves x (PartialProof x) (σ x))
(box_prop : ∀ x, (r 𝕏.α x).isBox →  -- on every path from the root to non-ax leaves there is a box node
  (∀ n, ∀ f : Fin (n + 1) → (PartialProof x).X,
    f 0 = (PartialProof x).root →
    (CutPre.r (PartialProof x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
    (∀ m : Fin n, CutPre.edge (PartialProof x).α (f m.castSucc) (f m.succ)) →
     ∃ m : Fin (n + 1), (CutPre.r (PartialProof x).α (f m)).isBox))
  : SplitCut.Proof := by exact -- ∀ x : 𝕏.X, 𝕐 ⊢ σ x
  { X := (y : 𝕏.X) × (PartialProof y).X
    α := ProofTranslationMap PartialProof
    step := by -- DONT DELETE THE PROOF BELOW, ITS COMMENTED FOR NOW BECAUSE ITS SO SLOW
    --  this is a lot of repetition! but I find that not using the intermediate 'ptm_eq' steps causes lean to oversimplify down to something harder to work from
          intro y_zy
          have h2 := (PartialProof y_zy.1).step y_zy.2
          cases r_def : (@CutPre.r _ _ _ _ (PartialProof y_zy.1).α y_zy.2) <;> simp [r_def, CutPre.fₙ_alternate] at h2
          case pre z _ =>
            have ptm_r_eq : SplitCut.r (ProofTranslationMap PartialProof) y_zy = SplitCut.RuleApp.skp (σ z) := by simp [SplitCut.r, ProofTranslationMap, r_def]
            have ptm_p_eq : SplitCut.p (ProofTranslationMap PartialProof) y_zy = [⟨z, (PartialProof z).root⟩] := by simp [SplitCut.p, ProofTranslationMap, r_def]
            simp [ptm_r_eq, ptm_p_eq, ProofTranslation_f]
            simp [SplitCut.f]
            exact root_proves z
          case cutₗ Δ φ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.cutₗ Δ φ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case cutᵣ Δ φ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.cutᵣ Δ φ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case wkₗ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.wkₗ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case wkᵣ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.wkᵣ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case topₗ Δ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.topₗ Δ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case topᵣ Δ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.topᵣ Δ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axₗₗ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axₗₗ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axₗᵣ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axₗᵣ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axᵣₗ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axᵣₗ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case axᵣᵣ Δ n in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.axᵣᵣ Δ n in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, ←h2]
          case orₗ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.orₗ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case orᵣ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.orᵣ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case andₗ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.andₗ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case andᵣ Δ φ ψ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.andᵣ Δ φ ψ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, ←h2]
          case boxₗ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.boxₗ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
          case boxᵣ Δ φ in_Δ =>
            have ptm_eq : ProofTranslationMap PartialProof y_zy = ⟨SplitCut.RuleApp.boxᵣ Δ φ in_Δ, (CutPre.p (PartialProof y_zy.1).α y_zy.2).map (fun z ↦ ⟨y_zy.1, z⟩)⟩ := by simp [ProofTranslationMap, r_def]
            simp [SplitCut.p, ptm_eq, ProofTranslation_f]
            rw [SplitCut.r]
            simp [ptm_eq, SplitCut.fₙ_alternate, h2]
    path := by
      intro ⟨y, z_y⟩ ⟨f, ⟨f_zero, f_succ⟩⟩
      have lex_chain : ∀ (n : ℕ), Sigma.Lex (edge 𝕏.α) (fun x ↦ CutPre.edge (PartialProof x).α) (f n) (f (n + 1)) := by
        intro n
        have := f_succ n
        unfold ProofTranslationMap SplitCut.edge at this
        simp [SplitCut.p] at this
        rcases r_def : CutPre.r (PartialProof (f n).1).α (f n).2 <;> simp [r_def] at this
        case pre z z_in =>
          apply Sigma.Lex.left
          convert z_in
          simp [this]
        all_goals
          have ⟨z, z_prop, eq⟩ := this
          apply Sigma.lex_iff.2 (Or.inr ⟨?_, ?_⟩)
          · grind
          · simp [CutPre.edge]
            have eq1 : (f n).1 = (f (n + 1)).1 := by grind
            have eq2 : (f (n + 1)).2 = eq1 ▸ z := by grind
            convert z_prop
            grind
      by_cases h : ∀ n, ∃ m ≥ n, ∀ (h : (f m).1 = (f (m + 1)).1), ¬ (CutPre.edge (PartialProof (f m).1).α (f m).2 (h ▸ (f (m + 1)).2))--(obviously change later)
      case neg =>
        simp at h
        intro l
        have ⟨n, n_prop⟩ := h
        have h : ∀ m ≥ n, (f n).1 = (f m).1 := by
          intro m m_ge
          induction m
          case zero =>
            simp at m_ge
            subst m_ge
            rfl
          case succ k ih =>
            by_cases eq : n = k + 1
            · subst eq
              rfl
            · rw [ih (by omega)]
              exact (n_prop k (by omega)).choose
        let g : ℕ → (PartialProof (f n).1).X := fun m ↦ h (n + m) (by grind) ▸ (f (n + m)).2
        have g_prop : ∀ (m : ℕ), CutPre.edge (PartialProof (f n).fst).α (g m) (g (m + 1)) := by
          intro m
          unfold g
          have ⟨eq, edge⟩ := n_prop (n + m) (by omega)
          -- have h : f (n + (m + 1)) = f (n + m + 1) := by grind
          grind
        have ⟨m, m_prop⟩ := (PartialProof (f n).1).path (f n).2 ⟨g, by unfold g; simp, g_prop⟩ l
        use n + m
        unfold g at m_prop
        simp_all
        convert m_prop
        have := h (l + n + m) (by omega)
        have := h (l + (n + m)) (by omega)
        convert ProofTranslation_isBox PartialProof (f (l + n + m)) using 4
        · linarith
        · congr
          simp_all
          have h : ∀ α : Type, ∀ β : α → Type, ∀ z₁ : (a : α) × β a, ∀ z₂, z₁ = z₂ → z₁.2 ≍ z₂.2 := by simp?
          apply h
          grind
      case pos =>
        simp [ProofTranslation_isBox]
        let g : ℕ → 𝕏.X := fun n ↦ (@dep_sum_seq_proj 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h n).1
        have g_prop : ∀ n, edge 𝕏.α (g n) (g (n + 1)) := by
          apply @infinite_dep_sum_chain
          exact lex_chain
        intro n
        have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_prop (@dep_sum_seq_proj 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h n).2
        apply @infinite_dep_sum_chain_inf 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h (fun x ↦ (r 𝕏.α x).isBox) (fun ⟨x, z⟩ ↦ (CutPre.r (PartialProof x).α z).isBox)
                (inf_path_has_inf_boxes g g_prop) ?_
        intro n n_is_box
        simp
        let f_sub := @infinite_dep_sum_chain_finite_subchain 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h n
        have f_sub_prop := @infinite_dep_sum_chain_finite_subchain_prop 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h n
        have ⟨⟨m, m_lt⟩, m_prop⟩ := box_prop _ n_is_box _ f_sub ?_ ?_ f_sub_prop
        · unfold f_sub infinite_dep_sum_chain_finite_subchain at m_prop
          simp at m_prop
          use m
          convert m_prop
          · rw [←infinite_dep_sum_sequence_proj_eq]
            apply Eq.symm $ @fst_same_in_range 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h _ _ ?_ ?_ <;> grind
          · grind
        · unfold f_sub infinite_dep_sum_chain_finite_subchain
          cases n <;> simp [dep_sum_seq_proj]
          case zero =>
            have ⟨_, prop⟩ := Nat.find_spec (h 0)
            have := f_succ $ Nat.find (h 0)
            unfold ProofTranslationMap SplitCut.edge SplitCut.p at this
            rcases r_def : CutPre.r (PartialProof (f (Nat.find (h 0))).1).α (f (Nat.find (h 0))).2 <;> simp only [r_def, List.mem_singleton] at this
            case pre z z_in =>
              have fst_eq := (Sigma.ext_iff.1 this).1
              simp only at fst_eq
              have ⟨t_eq, snd_eq⟩ := heq_iff_exists_eq_cast.1 (Sigma.ext_iff.1 this).2
              simp only [snd_eq]
              apply Eq.symm
              apply eq_cast_iff_heq.2
              rw [←fst_eq]
            all_goals
              exfalso
              simp only [List.mem_map] at this
              have ⟨z, z_in, z_eq⟩ := this
              apply prop
              · unfold CutPre.edge
                convert z_in
                have ⟨t_eq, snd_eq⟩ := heq_iff_exists_eq_cast.1 (Sigma.ext_iff.1 z_eq).2
                apply Eq.symm
                simp only at snd_eq
                convert snd_eq
                grind
              · have fst_eq := (Sigma.ext_iff.1 z_eq).1
                rw [←fst_eq]
          case succ n =>
            let ih := (@dep_sum_seq_proj 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h n).2
            have ⟨_, prop⟩ := Nat.find_spec (h ih)
            have := f_succ $ Nat.find (h ih)
            unfold ProofTranslationMap SplitCut.edge SplitCut.p at this
            rcases r_def : CutPre.r (PartialProof (f (Nat.find (h ih))).1).α (f (Nat.find (h ih))).2 <;> simp only [r_def, List.mem_singleton] at this
            case pre z z_in =>
              have fst_eq := (Sigma.ext_iff.1 this).1
              simp only at fst_eq
              have ⟨t_eq, snd_eq⟩ := heq_iff_exists_eq_cast.1 (Sigma.ext_iff.1 this).2
              simp only [snd_eq]
              apply Eq.symm
              apply eq_cast_iff_heq.2
              rw [←fst_eq]
            all_goals
              exfalso
              simp only [List.mem_map] at this
              have ⟨z, z_in, z_eq⟩ := this
              apply prop
              · unfold CutPre.edge
                convert z_in
                have ⟨t_eq, snd_eq⟩ := heq_iff_exists_eq_cast.1 (Sigma.ext_iff.1 z_eq).2
                apply Eq.symm
                simp only at snd_eq
                convert snd_eq
                grind
              · have fst_eq := (Sigma.ext_iff.1 z_eq).1
                rw [←fst_eq]
        · unfold f_sub infinite_dep_sum_chain_finite_subchain
          simp
          let ih := (@dep_sum_seq_proj 𝕏.X (fun x ↦ (PartialProof x).X) f (fun x ↦ CutPre.edge (PartialProof x).α) h n).2
          have ⟨_, prop⟩ := Nat.find_spec (h ih)
          have := f_succ $ Nat.find (h ih)
          unfold ProofTranslationMap SplitCut.edge SplitCut.p at this
          rcases r_def : CutPre.r (PartialProof (f (Nat.find (h ih))).1).α (f (Nat.find (h ih))).2 <;> simp only [r_def, List.mem_singleton] at this
          case pre z z_in =>
            have isNonAx : (CutPre.r (PartialProof (f (Nat.find (h ih) )).fst).α (f (Nat.find (h ih) )).snd).isNonAxLeaf := by simp [r_def, CutPre.RuleApp.isNonAxLeaf]
            convert isNonAx
            · simp [←infinite_dep_sum_sequence_proj_eq]
              apply fst_same_in_range <;> grind
            · have eq : ih + (Nat.find (h ih) - ih) = Nat.find (h ih) := by grind
              grind
          all_goals
            exfalso
            simp only [List.mem_map] at this
            have ⟨z, z_in, z_eq⟩ := this
            apply prop
            · unfold CutPre.edge
              convert z_in
              have ⟨t_eq, snd_eq⟩ := heq_iff_exists_eq_cast.1 (Sigma.ext_iff.1 z_eq).2
              apply Eq.symm
              simp only at snd_eq
              convert snd_eq
              grind
            · have fst_eq := (Sigma.ext_iff.1 z_eq).1
              rw [←fst_eq]}
