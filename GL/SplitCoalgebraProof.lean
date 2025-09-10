import GL.CoalgebraProof

namespace split

universe u

def SplitFormula.isDiamond : Formula ⊕ Formula -> Prop
  | Sum.inl (◇_) => true
  | Sum.inr (◇_) => true
  | _ => false

def SplitFormula.opUnDi (A : Formula ⊕ Formula) : Option (Formula ⊕ Formula) := match A with
  | Sum.inl (◇B) => Option.some (Sum.inl B)
  | Sum.inr (◇B) => Option.some (Sum.inr B)
  | _ => none

instance : DecidablePred SplitFormula.isDiamond := by
  intro A
  rcases A with A | A
  all_goals
  cases A <;> simp [SplitFormula.isDiamond]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp

def D (Γ : Finset (Formula ⊕ Formula)) : Finset (Formula ⊕ Formula)
  := Finset.filter SplitFormula.isDiamond Γ ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  rcases A with A | A <;> rcases B with B | B <;> rcases C with C | C
  all_goals
  simp_all
  cases A <;> cases B
  all_goals
    simp_all [SplitFormula.opUnDi])

inductive RuleApp
  | topₗ : RuleApp
  | topᵣ : RuleApp
  | axₗₗ : Nat → RuleApp
  | axₗᵣ : Nat → RuleApp
  | axᵣₗ : Nat → RuleApp
  | axᵣᵣ : Nat → RuleApp
  | andₗ : Formula → Formula → RuleApp
  | andᵣ : Formula → Formula → RuleApp
  | orₗ : Formula → Formula → RuleApp
  | orᵣ : Formula → Formula → RuleApp
  | boxₗ : Formula → RuleApp
  | boxᵣ : Formula → RuleApp

@[simp] def T : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨⟨λ X ↦ ((RuleApp × Finset (Formula ⊕ Formula) × Multiset X) : Type u), by rintro X Y f ⟨r, Γ, A⟩; exact ⟨r, Γ, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩

def fₚ : RuleApp → Finset (Formula ⊕ Formula)
  | RuleApp.topₗ => {Sum.inl ⊤}
  | RuleApp.topᵣ => {Sum.inr ⊤}
  | RuleApp.axₗₗ n => {Sum.inl $ at n, Sum.inl $ na n}
  | RuleApp.axₗᵣ n => {Sum.inl $ at n, Sum.inr $ na n}
  | RuleApp.axᵣₗ n => {Sum.inr $ at n, Sum.inl $ na n}
  | RuleApp.axᵣᵣ n => {Sum.inr $ at n, Sum.inr $ na n}
  | RuleApp.andₗ A B => {Sum.inl (A & B)}
  | RuleApp.andᵣ A B => {Sum.inr (A & B)}
  | RuleApp.orₗ A B => {Sum.inl (A v B)}
  | RuleApp.orᵣ A B => {Sum.inr (A v B)}
  | RuleApp.boxₗ A => {Sum.inl (□ A)}
  | RuleApp.boxᵣ A => {Sum.inr (□ A)}

def isBox : RuleApp → Prop
  | RuleApp.boxₗ _ => True
  | RuleApp.boxᵣ _ => True
  | _ => False

def r {X : Type u} (α : X → T.obj X) (x : X) := (α x).1
def fₙ {X : Type u} (α : X → T.obj X) (x : X) := (α x).2.1
def f {X : Type u} (α : X → T.obj X) (x : X) := fₚ (r α x) ∪ fₙ α x
def p {X : Type u} (α : X → T.obj X) (x : X) := (α x).2.2
def edge  {X : Type u} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

structure GLSplitProof where
  X : Type u
  α : X → T.obj X
  lin : LinearOrder X
  h : ∀ (x : X), match r α x with
    | RuleApp.andₗ A B => (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inl A}, (fₙ α x) ∪ {Sum.inl B}}
    | RuleApp.andᵣ A B => (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inr A}, (fₙ α x) ∪ {Sum.inr B}}
    | RuleApp.orₗ A B => (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inl A, Sum.inl B}}
    | RuleApp.orᵣ A B => (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inr A, Sum.inr B}}
    | RuleApp.boxₗ A => (p α x).map (f α) = {D (fₙ α x) ∪ {Sum.inl A}}
    | RuleApp.boxᵣ A => (p α x).map (f α) = {D (fₙ α x) ∪ {Sum.inr A}}
    | _ => p α x = {}

instance instSetoidXSplit (𝕏 : GLSplitProof) : Setoid 𝕏.X where
  r x y := f 𝕏.α x = f 𝕏.α y
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot 𝕐 (x : Quotient (instSetoidXSplit 𝕐)) :=
  T.map (Quotient.mk (instSetoidXSplit 𝕐)) (𝕐.α (Quotient.out x))

/- FILTRATIONS -/

noncomputable def Filtration (𝕐 : GLSplitProof) : GLSplitProof where
  X := Quotient (instSetoidXSplit 𝕐)
  α := α_quot 𝕐
  lin := by sorry
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidXSplit 𝕐) x
      have claim : f (fun x ↦ (T.map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidXSplit 𝕐)))) (𝕐.α (Quotient.out x))) ∘ (fun x ↦ ⟦x⟧) = f 𝕐.α := by
        funext x
        rw [←(hyp x)]
        simp [f, fₚ, fₙ]
        sorry -- rewrite
      have h := 𝕐.h (@Quotient.out _ (instSetoidXSplit 𝕐) ⟦x⟧)
      sorry -- rewrite
      -- rcases h with ⟨bot1, bot2⟩ | ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩ | ⟨A, box1, box2⟩
      -- · refine Or.inl ⟨bot1, ?_⟩
      --   simp [p]
      --   exact bot2
      -- · refine Or.inr $ Or.inl ⟨bot1, ?_⟩
      --   simp [p]
      --   exact bot2
      -- · refine Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, and1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at and2
      --   rw [←and2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, and1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at and2
      --   rw [←and2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, or1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at or2
      --   rw [←or2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, or1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at or2
      --   rw [←or2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, box1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at box2
      --   rw [←box2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr ⟨A, box1, ?_⟩
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at box2
      --   rw [←box2]
      --   apply congr_arg₂ Multiset.map claim rfl

/- PARTIAL INTERPOLATION PROOFS -/
