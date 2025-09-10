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

def DSplit (Γ : Finset (Formula ⊕ Formula)) : Finset (Formula ⊕ Formula)
  := Finset.filter SplitFormula.isDiamond Γ ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  rcases A with A | A <;> rcases B with B | B <;> rcases C with C | C
  all_goals
  simp_all
  cases A <;> cases B
  all_goals
    simp_all [SplitFormula.opUnDi])

@[simp] def T (R : Set String) : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨⟨λ X ↦ (({x : String // x ∈ R} × Finset (Formula ⊕ Formula) × Finset (Formula ⊕ Formula) × Multiset X) : Type u), by rintro X Y f ⟨r, Γ₁, Γ₂, A⟩; exact ⟨r, Γ₁, Γ₂, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩

@[simp] def Rules : Set String := {"topₗ", "topᵣ", "axₗₗ", "axₗᵣ", "axᵣₗ", "axᵣᵣ", "orₗ", "orᵣ", "andₗ", "andᵣ", "boxₗ", "boxᵣ"}

def r {R : Set String} {X : Type u} (α : X → (T R).obj X) (x : X) := (α x).1
def fₚ {R : Set String} {X : Type u} (α : X → (T R).obj X) (x : X) := (α x).2.1
def fₙ {R : Set String} {X : Type u} (α : X → (T R).obj X) (x : X) := (α x).2.2.1
def f {R : Set String} {X : Type u} (α : X → (T R).obj X) (x : X) := fₚ α x ∪ fₙ α x
def p {R : Set String} {X : Type u} (α : X → (T R).obj X) (x : X) := (α x).2.2.2
def edge {R : Set String} {X : Type u} (α : X → (T R).obj X) (x y : X) : Prop := y ∈ p α x

structure GLSplitProof where
  X : Type u
  α : X → (T Rules).obj X
  h : ∀ (x : X),
        (fₚ α x = {Sum.inl Formula.bottom} ∧ p α x = {})
      ∨ (fₚ α x = {Sum.inr Formula.bottom} ∧ p α x = {})
      ∨ (∃ (n : ℕ), fₚ α x = {Sum.inl $ Formula.atom n, Sum.inl $ Formula.neg_atom n} ∧ p α x = {})
      ∨ (∃ (n : ℕ), fₚ α x = {Sum.inl $ Formula.atom n, Sum.inr $ Formula.neg_atom n} ∧ p α x = {})
      ∨ (∃ (n : ℕ), fₚ α x  = {Sum.inr $ Formula.atom n, Sum.inl $ Formula.neg_atom n} ∧ p α x = {})
      ∨ (∃ (n : ℕ), fₚ α x  = {Sum.inr $ Formula.atom n, Sum.inr $ Formula.neg_atom n} ∧ p α x = {})
      ∨ (∃ (A B : Formula), fₚ α x = {Sum.inl $ Formula.and A B} ∧ (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inl A}, (fₙ α x) ∪ {Sum.inl B}})
      ∨ (∃ (A B : Formula), fₚ α x = {Sum.inr $ Formula.and A B} ∧ (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inr A}, (fₙ α x) ∪ {Sum.inr B}})
      ∨ (∃ (A B : Formula), fₚ α x = {Sum.inl $ Formula.or A B} ∧ (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inl A, Sum.inl B}})
      ∨ (∃ (A B : Formula), fₚ α x = {Sum.inr $ Formula.or A B} ∧ (p α x).map (f α) = {(fₙ α x) ∪ {Sum.inr A, Sum.inr B}})
      ∨ (∃ (A : Formula), fₚ α x = {Sum.inl $ Formula.box A} ∧ (p α x).map (f α) = {DSplit (fₙ α x) ∪ {Sum.inl A}}) -- the condition i wrote on ipad needs to go here
      ∨ (∃ (A : Formula), fₚ α x = {Sum.inr $ Formula.box A} ∧ (p α x).map (f α) = {DSplit (fₙ α x) ∪ {Sum.inr A}}) -- the condition i wrote on ipad needs to go here

instance (𝕏 : GLSplitProof) : CategoryTheory.Endofunctor.Coalgebra (T Rules) where
  V := 𝕏.X
  str := 𝕏.α

instance instSetoidXSplit (𝕏 : GLSplitProof) : Setoid 𝕏.X where
  r x y := f 𝕏.α x = f 𝕏.α y
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot 𝕐 (x : Quotient (instSetoidXSplit 𝕐)) :=
  (T Rules).map (Quotient.mk (instSetoidXSplit 𝕐)) (𝕐.α (Quotient.out x))

/- FILTRATIONS -/

noncomputable def Filtration (𝕐 : GLSplitProof) : GLSplitProof where
  X := Quotient (instSetoidXSplit 𝕐)
  α := α_quot 𝕐
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidXSplit 𝕐) x
      have claim : f (fun x ↦ ((T Rules).map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidXSplit 𝕐)))) (𝕐.α (Quotient.out x))) ∘ (fun x ↦ ⟦x⟧) = f 𝕐.α := by
        funext x
        rw [←(hyp x)]
        simp [f, fₚ, fₙ]
      have h := 𝕐.h (@Quotient.out _ (instSetoidXSplit 𝕐) ⟦x⟧)
      rcases h with ⟨bot1, bot2⟩ | ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩ | ⟨A, box1, box2⟩
      · refine Or.inl ⟨bot1, ?_⟩
        simp [p]
        exact bot2
      · refine Or.inr $ Or.inl ⟨bot1, ?_⟩
        simp [p]
        exact bot2
      · refine Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
        simp [p]
        exact lem2
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
        simp [p]
        exact lem2
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
        simp [p]
        exact lem2
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨n, lem1, ?_⟩
        simp [p]
        exact lem2
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, and1, ?_⟩
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at and2
        rw [←and2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, and1, ?_⟩
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at and2
        rw [←and2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, or1, ?_⟩
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at or2
        rw [←or2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, B, or1, ?_⟩
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at or2
        rw [←or2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl ⟨A, box1, ?_⟩
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at box2
        rw [←box2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr ⟨A, box1, ?_⟩
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at box2
        rw [←box2]
        apply congr_arg₂ Multiset.map claim rfl

/- PARTIAL INTERPOLATION PROOFS -/
