import GL.Logic
import GL.CoalgebraProof
import GL.SplitCoalgebraProof
import Mathlib.Data.Fintype.Defs

/- SYSTEMS OF EQUATIONS -/

/-- Structure preserving map substituting Pₙ by C --/
def single (n : Nat) (C : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at k => if k == n then C else at k
  | na k => if k == n then ~ C else na k
  | A & B => (single n C A) & (single n C B)
  | A v B => (single n C A) v (single n C B)
  | □ A => □ (single n C A)
  | ◇ A => ◇ (single n C A)

/-- Structure preserving map substituting all atoms meeting a certain criteria p --/
def partial_ (p : Nat → Prop) [DecidablePred p] (σ : Subtype p → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : p n then σ ⟨n, h⟩ else at n
  | na n => if h : p n then ~ σ ⟨n, h⟩ else at n
  | A & B => (partial_ p σ A) & (partial_ p σ B)
  | A v B => (partial_ p σ A) v (partial_ p σ B)
  | □ A => □ (partial_ p σ A)
  | ◇ A => ◇ (partial_ p σ A)

/-- Structure preserving map substituting all atoms via a transformation σ --/
def full (σ : Nat → Formula) (A : Formula) : Formula := match A with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => σ n
  | na n => ~ (σ n)
  | A & B => (full σ A) & (full σ B)
  | A v B => (full σ A) v (full σ B)
  | □ A => □ (full σ A)
  | ◇ A => ◇ (full σ A)
termination_by Formula.size A
decreasing_by
  all_goals
  simp [Formula.size]
  try linarith

/- Shift all atoms up or down, might come in handy later --/
def shift_up (k : Nat) : Formula → Formula := full (λ n ↦ at (n + k))
def shift_down (k : Nat) : Formula → Formula := full (λ n ↦ at (n - k))

namespace split

def List.get_singleton {α : Type} (l : List α) (h : ∃ x, [x] = l) : α := match l with
  | [x] => x
  | [] => by exfalso; grind
  | x::y::xs => by exfalso; grind

-- universe u
-- inductive Formula_on {X : Type} : (vars : List X) → Type
--   | var {vars} : (x : X) → (h : vars = []) → Formula_on (x :: vars)
--   | bottom {vars} : Formula_on vars
--   | top {vars} : Formula_on vars
--   | atom {vars} : Nat → Formula_on vars
--   | neg_atom {vars} : Nat → Formula_on vars
--   | and {vars} : Formula_on vars → Formula_on vars → Formula_on vars
--   | or {vars} : Formula_on vars → Formula_on vars → Formula_on vars
--   | box {vars} : Formula_on vars → Formula_on vars
--   | diamond {vars} : Formula_on vars → Formula_on vars
-- deriving Repr,DecidableEq

-- def coe {X : Type} : Formula_on ([] : List X) → Formula
--   | .bottom => ⊥
--   | .top => ⊤
--   | .atom n => at n
--   | .neg_atom n => na n
--   | .and A B => (coe A) & (coe B)
--   | .or A B => (coe A) v (coe B)
--   | .box A => □ (coe A)
--   | .diamond A => ◇ (coe A)

-- def eoc {X : Type} : Formula → Formula_on ([] : List X)
--   | .bottom => .bottom
--   | .top => .top
--   | .atom n => .atom n
--   | .neg_atom n => .neg_atom n
--   | .and A B => .and (eoc A) (eoc B)
--   | .or A B => .or (eoc A) (eoc B)
--   | .box A => .box (eoc A)
--   | .diamond A => .diamond (eoc A)

-- instance {X : Type} : Equiv (Formula_on ([] : List X)) (Formula) where
--   toFun := coe
--   invFun := eoc
--   left_inv := by sorry
--   right_inv := by sorry


-- def equation (𝕏 : GLSplitProof) [fin : Fintype 𝕏.X] (x : 𝕏.X) : Formula_on fin.elems := match r 𝕏.α x with


def GLSplitProof.Sequent (𝕏 : GLSplitProof) [fin_X : Fintype 𝕏.X] : Finset Formula :=
  fin_X.elems.biUnion (fun x ↦ (f 𝕏.α x).image (Sum.elim id id))

def GLSplitProof.freeVar (𝕏 : GLSplitProof) [fin_X : Fintype 𝕏.X] : Nat :=
  Formula.sequent.Sequent.freshVar (GLSplitProof.Sequent 𝕏)

def GLSplitProof.Encode (𝕏 : GLSplitProof) [fin_X : Fintype 𝕏.X] {n : Nat} (bij : 𝕏.X ≃ Fin n) (x : 𝕏.X) :=
  GLSplitProof.freeVar 𝕏 + bij.toFun x

def equation (𝕏 : GLSplitProof) {n : Nat} [fin_X : Fintype 𝕏.X] (bij : 𝕏.X ≃ Fin n) (x : 𝕏.X) : Formula := match r : r 𝕏.α x with
  | RuleApp.topₗ => ⊥
  | RuleApp.topᵣ => ⊤
  | RuleApp.axₗₗ _ => ⊥
  | RuleApp.axₗᵣ k => na k
  | RuleApp.axᵣₗ k => at k
  | RuleApp.axᵣᵣ _ => ⊤
  | RuleApp.orₗ A B => match p : p 𝕏.α x with
    | [] => by exfalso ; sorry
    | [y] => at (GLSplitProof.Encode 𝕏 bij y)
    | x :: y :: xs => by exfalso; sorry
  | RuleApp.orᵣ A B => match p 𝕏.α x with
    | [] => by exfalso ; sorry
    | [y] => at (GLSplitProof.Encode 𝕏 bij y)
    | x :: y :: xs => by exfalso; sorry
  | RuleApp.andₗ A B => match p 𝕏.α x with
    | [] => by exfalso ; sorry
    | [y] => by exfalso ; sorry
    | x :: y :: [] => at (GLSplitProof.Encode 𝕏 bij x) v at (GLSplitProof.Encode 𝕏 bij y)
    | x :: y :: z :: xs => by exfalso; sorry
  | RuleApp.andᵣ A B => match p 𝕏.α x with
    | [] => by exfalso ; sorry
    | [y] => by exfalso ; sorry
    | x :: y :: [] => at (GLSplitProof.Encode 𝕏 bij x) & at (GLSplitProof.Encode 𝕏 bij y)
    | x :: y :: z :: xs => by exfalso; sorry
  | RuleApp.boxₗ A => match p 𝕏.α x with
    | [] => by exfalso ; sorry
    | [y] => ◇ at (GLSplitProof.Encode 𝕏 bij y)
    | x :: y :: xs => by exfalso; sorry
  | RuleApp.boxᵣ A => match p 𝕏.α x with
    | [] => by exfalso ; sorry
    | [y] => □ at (GLSplitProof.Encode 𝕏 bij y)
    | x :: y :: xs => by exfalso; sorry

theorem existsSolution (𝕏 : GLSplitProof) [fin_X : Fintype 𝕏.X] {n : Nat} (bij : 𝕏.X ≃ Fin n) :
  ∃ σ : Nat → Formula,
    (∀ x : 𝕏.X, σ (GLSplitProof.Encode 𝕏 bij x) ≅ full σ (equation 𝕏 bij x)) := by sorry
