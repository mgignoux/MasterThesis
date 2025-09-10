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

inductive RuleApp
  | top : RuleApp
  | ax : Nat → RuleApp
  | and : Formula → Formula → RuleApp
  | or : Formula → Formula → RuleApp
  | box : Formula → RuleApp

@[simp] def T : (CategoryTheory.Functor (Type u) (Type u)) :=
  ⟨⟨λ X ↦ ((RuleApp × Finset Formula × Multiset X) : Type u), by rintro X Y f ⟨r, Γ, A⟩; exact ⟨r, Γ, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩

def D (Γ : Finset Formula) : Finset Formula := Finset.filter Formula.isDiamond Γ ∪ Finset.filterMap Formula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  cases A <;> cases B
  all_goals
  simp_all [Formula.opUnDi])

def fₚ : RuleApp → Finset Formula
  | RuleApp.top => {⊤}
  | RuleApp.ax n => {at n, na n}
  | RuleApp.and A B => {A & B}
  | RuleApp.or A B => {A v B}
  | RuleApp.box A => {□ A}

def isBox : RuleApp → Prop
  | RuleApp.box _ => True
  | _ => False

def r {X : Type u} (α : X → T.obj X) (x : X) := (α x).1
def fₙ {X : Type u} (α : X → T.obj X) (x : X) := (α x).2.1
def f {X : Type u} (α : X → T.obj X) (x : X) := fₚ (r α x) ∪ fₙ α x
def p {X : Type u} (α : X → T.obj X) (x : X) := (α x).2.2
def edge  {X : Type u} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

structure GLProof where
  X : Type u
  α : X → T.obj X
  h : ∀ (x : X), match r α x with
    | RuleApp.top => p α x = {}
    | RuleApp.ax _ => p α x = {}
    | RuleApp.and A B => (p α x).map (f α) = {(fₙ α x) ∪ {A}, (fₙ α x) ∪ {B}}
    | RuleApp.or A B => (p α x).map (f α) = {(fₙ α x) ∪ {A, B}}
    | RuleApp.box A => (p α x).map (f α) = {D (fₙ α x) ∪ {A}}


instance (𝕏 : GLProof) : CategoryTheory.Endofunctor.Coalgebra T where
  V := 𝕏.X
  str := 𝕏.α

/- POINT GENERATION -/

@[simp] def α_point (𝕐 : GLProof) (x : 𝕐.X) : {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} → T.obj {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} :=
  fun y ↦ ⟨(𝕐.α y.1).1, (𝕐.α y.1).2.1,
          Multiset.pmap (fun x y ↦ ⟨x, y⟩) (𝕐.α y.1).2.2 (fun _ z_in ↦ Relation.ReflTransGen.tail y.2 z_in)⟩

def PointGeneratedProof (𝕐 : GLProof) (x : 𝕐.X) : GLProof where
  X := {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y }
  α := α_point 𝕐 x
  h := by
    intro ⟨y, y_in⟩
    have h := 𝕐.h y
    sorry -- need to be rewritten
    -- rcases h with ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩
    -- · refine Or.inl ⟨bot1, ?_⟩
    --   simp_all [p]
    -- · refine Or.inr (Or.inl ⟨n, lem1, ?_⟩)
    --   simp_all [p]
    -- · refine Or.inr (Or.inr (Or.inl ⟨A, B, and1, ?_⟩))
    --   simp_all [fₙ, p, Multiset.map_pmap]
    --   simp [←and2, f, fₚ, fₙ, Multiset.pmap_eq_map]
    -- · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, or1, ?_⟩)))
    --   simp_all [fₙ, p, Multiset.map_pmap]
    --   simp [←or2, f, fₚ, fₙ, Multiset.pmap_eq_map]
    -- · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨A, box1, ?_⟩)))
    --   simp_all [fₙ, p, Multiset.map_pmap]
    --   simp [←box2, f, fₚ, fₙ, Multiset.pmap_eq_map]

/- FILTRATIONS -/

instance instSetoidX (𝕏 : GLProof) : Setoid 𝕏.X where
  r x y := f 𝕏.α x = f 𝕏.α y
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

@[simp] noncomputable def α_quot 𝕐 (x : Quotient (instSetoidX 𝕐)) :=
  T.map (Quotient.mk (instSetoidX 𝕐)) (𝕐.α (Quotient.out x))

noncomputable def Filtration (𝕐 : GLProof) : GLProof where
  X := Quotient (instSetoidX 𝕐)
  -- x := ⟦𝕐.x⟧
  α := α_quot 𝕐
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidX 𝕐) x
      have claim : f (fun x ↦ (T.map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidX 𝕐)))) (𝕐.α (Quotient.out x))) ∘ (fun x ↦ ⟦x⟧) = f 𝕐.α := by
        funext x
        rw [←(hyp x)]
        simp [f, fₚ, fₙ]
        sorry -- redo this later
      have h := 𝕐.h (@Quotient.out _ (instSetoidX 𝕐) ⟦x⟧)
      sorry
      -- needs to be rewritten

      -- rcases h with ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩
      -- · refine Or.inl ⟨bot1, ?_⟩
      --   simp [p]
      --   exact bot2
      -- · refine Or.inr (Or.inl ⟨n, lem1, ?_⟩)
      --   simp [p]
      --   exact lem2
      -- · refine Or.inr (Or.inr (Or.inl ⟨A, B, and1, ?_⟩))
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at and2
      --   rw [←and2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, or1, ?_⟩)))
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at or2
      --   rw [←or2]
      --   apply congr_arg₂ Multiset.map claim rfl
      -- · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨A, box1, ?_⟩)))
      --   simp only [fₙ, α_quot, T, f, p, Multiset.map_map]
      --   simp only [fₙ] at box2
      --   rw [←box2]
      --   apply congr_arg₂ Multiset.map claim rfl

/- SMALL MODEL PROPERTY -/

-- theorem bleh {α} {a b : α} {p : α → Prop} : p a → a = b → p b := by intro h1 h2; aesop

-- instance {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : Finite (Setoid.classes (instSetoidX 𝕏)) := by
--   have := Setoid.finite_classes_ker (fun x ↦ (𝕏.α x).1 ∪ (𝕏.α x).2.1)
--   apply bleh this
--   apply Setoid.classes_inj.1
--   simp [Setoid.ker]
--   apply Setoid.ext_iff.2
--   unfold instSetoidX
--   simp [Function.onFun, f, fₚ, fₙ]
--   intro a b
--   constructor
--   · intro mp
--     sorry
--   · intro mpp
--     sorry

theorem loop_has_box_app (𝕏 : GLProof) (x : 𝕏.X) :
  (Relation.TransGen (edge 𝕏.α)) x x →
    ∃ (y : 𝕏.X), (Relation.ReflTransGen (edge 𝕏.α)) x y
      ∧ (Relation.ReflTransGen (edge 𝕏.α)) y x
      ∧ isBox (r 𝕏.α y) := by
  intro x_x
  cases x_x
  case single xex => sorry
  case tail => sorry

def GLProof.Proves (𝕏 : GLProof) (Δ : Finset Formula) : Prop := ∃ x : 𝕏.X, f 𝕏.α x = Δ
infixr:6 "⊢" => GLProof.Proves

def equiv (A : Formula) (B : Formula) : Prop :=
  (∃ (𝕏 : GLProof.{u}), 𝕏 ⊢ {~A, B}) ∧ (∃ (𝕏 : GLProof.{u}), 𝕏 ⊢ {A, ~B})
infixr:7 "≅" => equiv
