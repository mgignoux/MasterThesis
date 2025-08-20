import GL.Logic
import Mathlib.Data.Set.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Finset.Lattice.Basic

instance {α} [DecidableEq α] (Γ : Finset α) : Union {x // x ∈ Γ.powerset} where -- mathlib ????
  union A B := ⟨A ∪ B, by
    apply Finset.mem_powerset.2
    apply Finset.subset_iff.2
    intro x h
    rcases (Finset.mem_union.1 h) with h | h
    · apply Finset.mem_of_subset (Finset.mem_powerset.1 A.2) h
    · apply Finset.mem_of_subset (Finset.mem_powerset.1 B.2) h
    ⟩

universe u

-- instance T_functor (Γ : Finset Formula) : CategoryTheory.Functor (Type u) (Type u) where
--   obj := λ (X : Type u) ↦ ((Γ.powerset × Γ.powerset × Multiset X) : Type u)
--   map := λ f ⟨Γ₁, Γ₂, A⟩ ↦ ⟨Γ₁, Γ₂, A.map f⟩
--   map_id := by aesop_cat
--   map_comp := by aesop_cat

@[simp] def T {α : Type} : Finset α → (CategoryTheory.Functor (Type u) (Type u)) :=
  λ Γ ↦ ⟨⟨λ X ↦ ((Γ.powerset × Γ.powerset × Multiset X) : Type u), by rintro X Y f ⟨Γ₁, Γ₂, A⟩; exact ⟨Γ₁, Γ₂, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩

def D (Γ : Finset Formula) : Finset Formula := Finset.filter Formula.isDiamond Γ ∪ Finset.filterMap Formula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  cases A <;> cases B
  all_goals
  simp_all [Formula.opUnDi])

def fₚ {β} {Γ : Finset β} {X : Type u} (α : X → (T Γ).obj X) (x : X) : Finset β := (α x).1
def fₙ {β} {Γ : Finset β} {X : Type u} (α : X → (T Γ).obj X) (x : X) : Finset β := (α x).2.1
def f {β} [DecidableEq β] {Γ : Finset β} {X : Type u} (α : X → (T Γ).obj X) (x : X) : Finset β := fₚ α x ∪ fₙ α x
def p {β} {Γ : Finset β} {X : Type u} (α : X → (T Γ).obj X) (x : X) : Multiset X := (α x).2.2
def edge {β} {Γ : Finset β} {X : Type u} (α : X → (T Γ).obj X) (x y : X) : Prop := y ∈ p α x

structure InfiniteProof (Γ : Finset Formula) where
  X : Type u
  -- x : X
  α : X → (T Γ).obj X
  -- r : ∀ (y : X), Relation.ReflTransGen (edge α) x y
  h : ∀ (x : X),
        (fₚ α x = {Formula.bottom} ∧ p α x = {})
      ∨ (∃ (n : ℕ), fₚ α x  = {Formula.atom n, Formula.neg_atom n} ∧ p α x = {})
      ∨ (∃ (A B : Formula), fₚ α x = {Formula.and A B} ∧ (p α x).map (f α) = {(fₙ α x) ∪ {A}, (fₙ α x) ∪ {B}})
      ∨ (∃ (A B : Formula), fₚ α x = {Formula.or A B} ∧ (p α x).map (f α) = {(fₙ α x) ∪ {A, B}})
      ∨ (∃ (A : Formula), (fₚ α x : Finset _) = {Formula.box A} ∧ (p α x).map (f α) = {D (fₙ α x) ∪ {A}} ) -- the condition i wrote on ipad needs to go here

instance {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : CategoryTheory.Endofunctor.Coalgebra (T Γ) where
  V := 𝕏.X
  str := 𝕏.α

/- POINT GENERATION -/

def pg_alpha {Γ : Finset Formula} (𝕐 : InfiniteProof Γ) (x : 𝕐.X) : {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} → (Γ.powerset × Γ.powerset × Multiset {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y}) :=
  fun y ↦ ⟨(𝕐.α y.1).1, (𝕐.α y.1).2.1,
          Multiset.pmap (fun x y ↦ ⟨x, y⟩) (𝕐.α y.1).2.2 (fun _ z_in ↦ Relation.ReflTransGen.tail y.2 z_in)⟩

def PointGenerated {Γ : Finset Formula} (𝕐 : InfiniteProof Γ) (x : 𝕐.X) : InfiniteProof Γ where
  X := {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y }
  α := pg_alpha 𝕐 x
  h := by
    intro ⟨y, y_in⟩
    have h := 𝕐.h y
    rcases h with ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩
    · refine Or.inl ⟨bot1, ?_⟩
      simp_all [p, pg_alpha]
    · refine Or.inr (Or.inl ⟨n, lem1, ?_⟩)
      simp_all [p, pg_alpha]
    · refine Or.inr (Or.inr (Or.inl ⟨A, B, and1, ?_⟩))
      simp_all [fₙ, pg_alpha, p, Multiset.map_pmap]
      simp [←and2, f, fₚ, fₙ, pg_alpha, Multiset.pmap_eq_map]
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, or1, ?_⟩)))
      simp_all [fₙ, pg_alpha, p, Multiset.map_pmap]
      simp [←or2, f, fₚ, fₙ, pg_alpha, Multiset.pmap_eq_map]
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨A, box1, ?_⟩)))
      simp_all [fₙ, pg_alpha, p, Multiset.map_pmap]
      simp [←box2, f, fₚ, fₙ, pg_alpha, Multiset.pmap_eq_map]

/- FILTRATIONS -/

instance instSetoidX {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : Setoid 𝕏.X where
  r x y := f 𝕏.α x = f 𝕏.α y
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot Γ 𝕐 (x : Quotient (instSetoidX 𝕐)) :=
  (T Γ).map (Quotient.mk (instSetoidX 𝕐)) (𝕐.α (Quotient.out x))

noncomputable def InfiniteProof.Filtration {Γ : Finset Formula} (𝕐 : InfiniteProof Γ) : InfiniteProof Γ where
  X := Quotient (instSetoidX 𝕐)
  -- x := ⟦𝕐.x⟧
  α := α_quot Γ 𝕐
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidX 𝕐) x
      have claim : f (fun x ↦ ((T Γ).map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidX 𝕐)))) (𝕐.α (Quotient.out x))) ∘ (fun x ↦ ⟦x⟧) = f 𝕐.α := by
        funext x
        rw [←(hyp x)]
        simp [f, fₚ, fₙ]
      have h := 𝕐.h (@Quotient.out _ (instSetoidX 𝕐) ⟦x⟧)
      rcases h with ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩
      · refine Or.inl ⟨bot1, ?_⟩
        simp [p]
        exact bot2
      · refine Or.inr (Or.inl ⟨n, lem1, ?_⟩)
        simp [p]
        exact lem2
      · refine Or.inr (Or.inr (Or.inl ⟨A, B, and1, ?_⟩))
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at and2
        rw [←and2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, or1, ?_⟩)))
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at or2
        rw [←or2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨A, box1, ?_⟩)))
        simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
        simp only [fₙ] at box2
        rw [←box2]
        apply congr_arg₂ Multiset.map claim rfl

/- SMALL MODEL PROPERTY -/

theorem bleh {α} {a b : α} {p : α → Prop} : p a → a = b → p b := by intro h1 h2; aesop

instance {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : Finite (Setoid.classes (instSetoidX 𝕏)) := by
  have := Setoid.finite_classes_ker (fun x ↦ (𝕏.α x).1 ∪ (𝕏.α x).2.1)
  apply bleh this
  apply Setoid.classes_inj.1
  simp [Setoid.ker]
  apply Setoid.ext_iff.2
  unfold instSetoidX
  simp [Function.onFun, f, fₚ, fₙ]
  intro a b
  constructor
  · intro mp
    sorry
  · intro mpp
    sorry

def InfiniteProof.Proves {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) (Δ : Finset Formula) : Prop := ∃ x : 𝕏.X, f 𝕏.α x = Δ

infixr:6 "⊢" => InfiniteProof.Proves
