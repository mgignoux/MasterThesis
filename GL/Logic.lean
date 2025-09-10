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

inductive Formula : Type
  | bottom : Formula
  | top : Formula
  | atom : Nat → Formula
  | neg_atom : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | box : Formula → Formula
  | diamond : Formula → Formula
deriving Repr,DecidableEq

namespace Formula
prefix:70 "at" => atom
prefix:70 "na" => neg_atom
prefix:70 "□" => box
prefix:70 "◇" => diamond
infixr:6 "&" => and
infixr:6 "v" => or

instance : Bot (Formula) where bot := Formula.bottom
instance : Top (Formula) where top := Formula.top

def isAtomic : Formula -> Prop
  | at _ => true
  | _ => false

def isNegAtomic : Formula -> Prop
  | na _ => true
  | _ => false

def isDiamond : Formula -> Prop
  | ◇_ => true
  | _ => false

def opUnDi (A : Formula) : Option Formula := match A with
  | ◇ B => Option.some B
  | _ => none

def unDi (A : Formula) (h : A.isDiamond) : Formula := match A with
  | ◇ B => B

def isBox : Formula -> Prop
  | □_ => true
  | _ => false

instance : DecidablePred Formula.isAtomic := by
  intro A
  cases A <;> simp [isAtomic]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp

instance : DecidablePred isNegAtomic := by
  intro A
  cases A <;> simp [isNegAtomic]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp

instance : DecidablePred isDiamond := by
  intro A
  cases A <;> simp [isDiamond]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp

instance : DecidablePred isBox := by
  intro A
  cases A <;> simp [isBox]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp

def neg : Formula → Formula
  | ⊥ => ⊤
  | ⊤ => ⊥
  | at n => na n
  | na n => at n
  | A & B => (neg A) v (neg B)
  | A v B => (neg A) & (neg B)
  | □ A => ◇ (neg A)
  | ◇ A => □ (neg A)

prefix:5 "~" => Formula.neg
notation:55 φ:56 " ↣ " ψ:55 => (¬ φ) ∨ ψ
notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) & (ψ ↣ φ)

def P := at 0
def Q := at 1

def size : Formula → Nat
  | ⊥ => 0
  | ⊤ => 0
  | at _ => 1
  | na _ => 1
  | A & B => size A + size B + 1
  | A v B => size A + size B + 1
  | □ A => size A + 1
  | ◇ A => size A + 1

def pp_form : Formula → String
  | ⊥ => "⊥"
  | ⊤ => "⊤"
  | at n => "P" ++ Nat.toSubscriptString n
  | na n => "¬P" ++ Nat.toSubscriptString n
  | A & B => "(" ++ pp_form A ++ "∧" ++ pp_form B ++ ")"
  | A v B => "(" ++ pp_form A ++ "∨" ++ pp_form B ++ ")"
  | □ A => "□" ++ pp_form A
  | ◇ A => "◇" ++ pp_form A

def Sequent := Finset Formula

unsafe def pp_forms (Γ : Sequent) : String :=
  String.intercalate "," ((Quot.unquot Γ.val).map pp_form)

unsafe def labelPrint (fs : Sequent) : String := match (Quot.unquot fs.val) with
| [A] => match A with
          | ⊥ => "⊥"
          | _ & _ => "⋀"
          | _ v _ => "∨"
          | □ _ => "□"
          | _ => "?"
| [A, B] => if A.isAtomic ∧ B.isNegAtomic then "Ax" else if B.isAtomic ∧ A.isAtomic then "Ax" else "?"
| _ => "?"

def vocab : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na n => {n}
  | A & B => vocab A ∪ vocab B
  | A v B => vocab A ∪ vocab B
  | □ A => vocab A
  | ◇ A => vocab A

namespace sequent

def vocab (Γ : Finset Formula) : Finset Nat := Finset.biUnion Γ Formula.vocab

def FLClosed (Γ : Sequent) : Prop := by unfold Sequent at Γ; exact
  ∀ A ∈ Γ, match A with
    | ⊥ => ⊥ ∈ Γ
    | ⊤ => ⊤ ∈ Γ
    | at n => at n ∈ Γ
    | na n => na n ∈ Γ
    | A & B => A ∈ Γ ∧ B ∈ Γ
    | A v B => A ∈ Γ ∧ B ∈ Γ
    | □ A => A ∈ Γ
    | ◇ A => A ∈ Γ
