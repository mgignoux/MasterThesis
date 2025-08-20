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

prefix:70 "·" => Formula.atom
prefix:70 "`·" => Formula.neg_atom
prefix:70 "□" => Formula.box
prefix:70 "◇" => Formula.diamond
infixr:6 "∧ᴳ" => Formula.and
infixr:6 "∨ᴳ" => Formula.or

instance : Bot (Formula) where bot := Formula.bottom
instance : Top (Formula) where top := Formula.top

def Formula.isAtomic : Formula -> Prop
  | ·_ => true
  | _ => false

def Formula.isNegAtomic : Formula -> Prop
  | `·_ => true
  | _ => false

def Formula.isDiamond : Formula -> Prop
  | ◇_ => true
  | _ => false

def Formula.opUnDi (A : Formula) : Option Formula := match A with
  | ◇ B => Option.some B
  | _ => none

def Formula.unDi (A : Formula) (h : A.isDiamond) : Formula := match A with
  | ◇ B => B

def Formula.isBox : Formula -> Prop
  | □_ => true
  | _ => false

instance : DecidablePred Formula.isAtomic := by
  intro A
  cases A <;> simp [Formula.isAtomic]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp

instance : DecidablePred Formula.isNegAtomic := by
  intro A
  cases A <;> simp [Formula.isNegAtomic]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp

instance : DecidablePred Formula.isDiamond := by
  intro A
  cases A <;> simp [Formula.isDiamond]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp

instance : DecidablePred Formula.isBox := by
  intro A
  cases A <;> simp [Formula.isBox]
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isFalse; simp
  · apply Decidable.isTrue;  simp
  · apply Decidable.isFalse; simp

def Formula.neg : Formula → Formula
  | ⊥ => ⊤
  | ⊤ => ⊥
  | · n => `· n
  | `· n => · n
  | A ∧ᴳ B => (Formula.neg A) ∨ᴳ (Formula.neg B)
  | Formula.or A B => (Formula.neg A) ∧ᴳ (Formula.neg B)
  | Formula.box A => ◇ (Formula.neg A)
  | Formula.diamond A => □ (Formula.neg A)

prefix:5 "¬ᴳ" => Formula.neg
notation:55 φ:56 " ↣ " ψ:55 => ¬ᴳ φ ∨ᴳ ψ
notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) ∧ᴳ (ψ ↣ φ)

def P := ·0
def Q := ·1

def pp_form : Formula → String
  | ⊥ => "⊥"
  | ⊤ => "⊤"
  | · n => "P" ++ Nat.toSubscriptString n
  | `· n => "¬P" ++ Nat.toSubscriptString n
  | A ∧ᴳ B => "(" ++ pp_form A ++ "∧" ++ pp_form B ++ ")"
  | A ∨ᴳ B => "(" ++ pp_form A ++ "∨" ++ pp_form B ++ ")"
  | □ A => "□" ++ pp_form A
  | ◇ A => "◇" ++ pp_form A

unsafe def pp_forms (Γ : Finset Formula) : String :=
  String.intercalate "," ((Quot.unquot Γ.val).map pp_form)

unsafe def labelPrint (fs : Finset Formula) : String := match (Quot.unquot fs.val) with
| [A] => match A with
          | ⊥ => "⊥"
          | _ ∧ᴳ _ => "⋀"
          | _ ∨ᴳ _ => "∨"
          | □ _ => "□"
          | _ => "?"
| [A, B] => if A.isAtomic ∧ B.isNegAtomic then "Ax" else if B.isAtomic ∧ A.isAtomic then "Ax" else "?"
| _ => "?"

def FLClosed (Γ : Finset Formula) : Prop :=
  ∀ A ∈ Γ, match A with
    | Formula.bottom => Formula.bottom ∈ Γ
    | Formula.top => Formula.top ∈ Γ
    | Formula.atom n => Formula.atom n ∈ Γ
    | Formula.neg_atom n => Formula.neg_atom n ∈ Γ
    | Formula.and A B => A ∈ Γ ∧ B ∈ Γ
    | Formula.or A B => A ∈ Γ ∧ B ∈ Γ
    | Formula.box A => A ∈ Γ
    | Formula.diamond A => A ∈ Γ
