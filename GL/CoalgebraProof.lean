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


universe u

-- instance T_functor (Γ : Finset Formula) : CategoryTheory.Functor (Type u) (Type u) where
--   obj := λ (X : Type u) ↦ ((Γ.powerset × Γ.powerset × Multiset X) : Type u)
--   map := λ f ⟨Γ₁, Γ₂, A⟩ ↦ ⟨Γ₁, Γ₂, A.map f⟩
--   map_id := by aesop_cat
--   map_comp := by aesop_cat

def T {α : Type} : Finset α → (CategoryTheory.Functor (Type u) (Type u)) :=
  λ Γ ↦ ⟨⟨λ X ↦ ((Γ.powerset × Γ.powerset × Multiset X) : Type u), by rintro X Y f ⟨Γ₁, Γ₂, A⟩; exact ⟨Γ₁, Γ₂, A.map f⟩⟩, by aesop_cat, by aesop_cat⟩


def fₚ {Γ : Finset Formula} {X : Type u} (α : X → (T Γ).obj X) (x : X) : Finset Formula := (α x).1
def fₙ {Γ : Finset Formula} {X : Type u} (α : X → (T Γ).obj X) (x : X) : Finset Formula := (α x).2.1
def f {Γ : Finset Formula} {X : Type u} (α : X → (T Γ).obj X) (x : X)  : Finset Formula := fₚ α x ∪ fₙ α x
def p {Γ : Finset Formula} {X : Type u} (α : X → (T Γ).obj X) (x : X)  : Multiset X := (α x).2.2


-- def BotRule (fs : Finset Formula) := fs = {Formula.bottom}
-- def LemRule (fs : Finset Formula) := ∃ (n : ℕ), fs = {Formula.atom n, Formula.neg_atom n}
-- def AndRule (fs : Finset Formula) :=  ∃ (A B : Formula), fs = {Formula.and A B}
-- def OrRule  (fs : Finset Formula) := ∃ (A B : Formula), fs = {Formula.or A B}
-- def BoxRule (fs : Finset Formula) := ∃ (A : Formula), fs = {Formula.box A}
-- instance (fs : Finset Formula) : Decidable (BotRule fs) := Finset.decidableEq fs {Formula.bottom}
-- instance (fs : Finset Formula) : Decidable (LemRule fs) :=  --- something to ask Malvin about
--   if h : fs.card = 2
--     then by sorry
--     else by
--       apply isFalse
--       intro con
--       have ⟨a, b⟩ := con
--       rw [b] at h
--       simp_all
-- instance (fs : Finset Formula) : Decidable (AndRule fs) := by sorry
-- instance (fs : Finset Formula) : Decidable (OrRule fs) := by sorry
-- instance (fs : Finset Formula) : Decidable (BoxRule fs) := by sorry

structure InfiniteProof (Γ : Finset Formula) where
  X : Type u
  x : X
  α : X → (T Γ).obj X
  r : ∀ (y : X), Relation.ReflTransGen (λ x y ↦ y ∈ (α x).2.2) x y
  h : ∀ (x : X),
        (fₚ α x = {Formula.bottom} ∧ p α x = {})
      ∨ (∃ (n : ℕ), fₚ α x = {Formula.atom n, Formula.neg_atom n} ∧ p α x = {}) -- (p α x).map (f α) has type Multiset (Finset Formula)
      ∨ (∃ (A B : Formula), fₚ α x = {Formula.and A B} ∧ (p α x).map (f α) = {(fₚ α x) ∪ {A}, (fₚ α x) ∪ {B}})
      ∨ (∃ (A B : Formula), fₚ α x = {Formula.or A B} ∧ (p α x).map (f α) = {(fₚ α x) ∪ {A, B}})
      ∨ (∃ (A : Formula), fₚ α x = {Formula.box A} ∧ True ) -- the condition i wrote on ipad needs to go here

def edge {Γ : Finset Formula} {𝕏 : InfiniteProof Γ} (x y : 𝕏.X) : Prop := y ∈ p 𝕏.α x

instance {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : CategoryTheory.Endofunctor.Coalgebra (T Γ) where
  V := 𝕏.X
  str := 𝕏.α

instance {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : Setoid 𝕏.X where
  r x y := fₚ 𝕏.α x = fₚ 𝕏.α y ∧ fₙ 𝕏.α x = fₙ 𝕏.α y
  iseqv := ⟨by intro x; exact ⟨rfl, rfl⟩,
            by intro x y h; exact ⟨Eq.symm h.1, Eq.symm h.2⟩,
            by intro x y z h1 h2; exact ⟨Eq.trans h1.1 h2.1, Eq.trans h1.2 h2.2⟩⟩

noncomputable def Filtration {Γ : Finset Formula} (𝕐 : InfiniteProof Γ) : InfiniteProof Γ where
  X := Quotient (instSetoidX 𝕐)
  x := ⟦𝕐.x⟧
  α x := ((T Γ).map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidX 𝕐)))) (𝕐.α (Quotient.out x))
  r := by
    have assump : @Quotient.out _ (instSetoidX 𝕐) ⟦𝕐.x⟧ = 𝕐.x := by sorry
    intro y
    cases y using Quotient.inductionOn
    case h y =>
      induction 𝕐.r y
      case refl => exact Relation.ReflTransGen.refl
      case tail b y x_b b_y ih =>
        apply Relation.ReflTransGen.tail ih
        have := fun x ↦ @Quotient.mk_out _ (instSetoidX 𝕐) x
    --   simp only [T, hyp]
        simp only [T]
        apply Multiset.mem_map_of_mem
        convert b_y
        sorry
  h := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (instSetoidX 𝕐) x
      have claim : f (fun x ↦ ((T Γ).map (fun (x : 𝕐.X) ↦ (⟦x⟧ : Quotient (instSetoidX 𝕐)))) (𝕐.α (Quotient.out x))) ∘ (fun x ↦ ⟦x⟧) = f 𝕐.α := by
        funext x
        simp [f]
        rw [←(hyp x).1, ←(hyp x).2]
        simp [T, fₚ, fₙ]
      have h := 𝕐.h (@Quotient.out _ (instSetoidX 𝕐) ⟦x⟧)
      rcases h with ⟨bot1, bot2⟩ | ⟨n, lem1, lem2⟩ | ⟨A, B, and1, and2⟩ | ⟨A, B, or1, or2⟩ | ⟨A, box1, box2⟩
      · apply Or.inl
        refine ⟨bot1, ?_⟩
        simp [p, T]
        exact bot2
      --  exact bot2
      · refine Or.inr (Or.inl ⟨n, lem1, ?_⟩)
        simp [p, T]
        exact lem2
      · refine Or.inr (Or.inr (Or.inl ⟨A, B, and1, ?_⟩))
        simp only [fₚ, T, f, p, Multiset.map_map]
        simp only [fₚ] at and2
        rw [←and2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, or1, ?_⟩)))
        simp only [fₚ, T, f, p, Multiset.map_map]
        simp only [fₚ] at or2
        rw [←or2]
        apply congr_arg₂ Multiset.map claim rfl
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨A, box1, ?_⟩)))
        simp -- cant do this until we add the condition later

instance {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) : Finite (Filtration 𝕏).X := by sorry

def InfiniteProof.Proves {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) (Δ : Finset Formula) : Prop := ∃ x : 𝕏.X, f 𝕏.α x = Δ

infixr:6 "⊢" => InfiniteProof.Proves




-- here we need to find a path downward from z to a root, which should always be possible. then we just search up from the root
theorem Upwards_inductionOn {Γ : Finset Formula} {𝕏 : InfiniteProof Γ} z
    {motive : 𝕏.X → Prop}
    (root : motive 𝕏.x)
    (step : (x : 𝕏.X) → motive x → ∀ {y}, (x_y : edge x y) → motive y)
    : motive z := by
  have x_z := 𝕏.r z
  induction x_z
  case refl => exact root
  case tail y z x_y y_z ih => exact step y ih y_z

-- should also be a downwards induction principal
