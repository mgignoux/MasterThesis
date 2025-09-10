import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! # Ideas for a unified modal formula type -/


/-! ## The general `Formula` type -/

inductive Formula (β : Type): Type
  | Top : Formula β
  | P : Nat → Formula β
  | Neg : Formula β  → Formula β -- Added.. Think we need this?
  | Con : Formula β → Formula β → Formula β
  | Box : β → Formula β  → Formula β
  | Mu : (Nat → Formula β) → Formula β -- Added

-- μx.□x
example : Formula Unit := Formula.Mu (fun x ↦ Formula.Box () (Formula.P x))

-- issue: This causes every logic we define to have a fixed point operator.
-- fix: make having a fixed point operator a condition?

inductive Formula' (β : Type) (α : Bool) : Type
  | Top : Formula' β α
  | P : Nat → Formula' β α
  | Neg : Formula' β α → Formula' β α
  | Con : Formula' β α → Formula' β α → Formula' β α
  | Box : β → Formula' β α → Formula' β α
  | Mu : α = true → (Nat → Formula' β α) → Formula' β α

-- μx.□x
def MuForm := Formula' Unit true
example : MuForm := Formula'.Mu rfl (fun x ↦ Formula'.Box () (Formula'.P x))

-- Not done: we need that variables are bound positively. So how do we add this?
-- Can we bake it into the inductive type? That would be great but how?
-- Other solution: Make it a subtype

def Atoms {β : Type} (A : Formula' β true) : Finset ℕ := match A with
  | Formula'.Top => {}
  | Formula'.P n => {n}
  | Formula'.Neg A => Atoms A
  | Formula'.Con A B => Atoms A ∪ Atoms B
  | Formula'.Box _ A => Atoms A
  | Formula'.Mu _ f => Atoms (f 0) ∩ Atoms (f 1)  -- True atoms which are not being used as variables will be in the intersection

def Pos {β : Type} (A : Formula' β true) (n : ℕ) : Prop := match A with
  | Formula'.Top => True
  | Formula'.P _ => True
  | Formula'.Neg (Formula'.P k) => k ≠ n
  | Formula'.Neg A => ¬(Pos A n)
  | Formula'.Con A B => Pos A n ∧ Pos B n
  | Formula'.Box _ A => Pos A n
  | Formula'.Mu _ f => Pos (f (n + 1)) n -- P n occours postively and is not the bound variable

def Pos_underBound {β : Type} (A : Formula' β true) : Prop := match A with
  | Formula'.Top => True
  | Formula'.P _ => True
  | Formula'.Neg A => Pos_underBound A
  | Formula'.Con A B => Pos_underBound A ∧ Pos_underBound B
  | Formula'.Box _ A => Pos_underBound A
  | Formula'.Mu h f => ∀ n ∉ Atoms (Formula'.Mu h f), Pos (f n) n -- P n occours postively and is not an atom

def MuForm' (β) := {A : Formula' β true // Pos_underBound A}

example : MuForm' Unit := ⟨Formula'.Mu rfl (fun x ↦ Formula'.Box () (Formula'.P x)), by
  intro n n_notin
  simp_all only [Atoms, Pos]⟩


instance {β k} : OfNat (Formula β) k := ⟨Formula.P k⟩
notation "⊤" => Formula.Top
notation φ1 "&" φ2 => Formula.Con φ1 φ2 -- FIXME add precedence?
notation "⌈" b "⌉" φ => Formula.Box b φ

-- Here is "still" polymorphic formula.
example {β} : Formula β := 1 & 2 & ⊤


/-! ## Examples -/

-- (1) Propositional Logic

def PropForm := Formula Empty

example : PropForm := 0 & 1 & 3

-- No box formulas since no maps from Empty.

-- (2) Basic Modal Logic

def ModForm := Formula Unit

prefix:55 "□" => Formula.Box ()

example : ModForm := □□□42


-- (3) Propositional Dynamic Logic
-- Here γ is the type of the atomic programs.

inductive Prog (γ : Type)
  | Atom : γ → Prog γ
  | Cup : Prog γ → Prog γ → Prog γ
  | Seq : Prog γ → Prog γ → Prog γ
  | Star : Prog γ → Prog γ
  | Test : Formula (Prog γ) → (Prog γ) -- Nice that this just works!

abbrev PDLForm γ := Formula (Prog γ)

instance {k} : OfNat (Prog Nat) k := ⟨Prog.Atom k⟩
example : PDLForm Nat := ⌈1⌉ ⊤

instance : Coe Char (Prog Char) := ⟨Prog.Atom⟩
example : PDLForm Char := ⌈'a'⌉⌈'b'⌉⌈'a'⌉ ⊤


-- (4) Epistemic Logic
-- Here α is the type of agents.

def EpForm α := Formula α


def Ag := { i : Nat // i ∈ [1,2,3] }

def a : Ag := ⟨1, by simp⟩

notation "Knows" => Formula.Box
example : EpForm { i : Nat // i ∈ [1,2,3] } := Knows a ⊤


-- (5) Public Announcement Logic

-- Naive def for Public Announcement Logic, not possible?
-- Note that `Formula PropForm` does not include [![!φ₁]φ₂]ψ etc.

-- def SelfPALForm := Formula SelfPALForm -- not possible?

def BrokenPALForm := Formula (Formula (Formula (/-...-/ sorry))) -- not viable.

-- And we want PALForm to extend EpForm, ideally with a `Coe`.

-- We wrap up announcements with a bang.
inductive PA : Type
 | Bang : Formula PA → PA

-- PROBLEM: no agents in the announcement then?!

/-- An agent or a public announcement -/
def PAL α := α ⊕ PA

def PALForm α := Formula (PAL α)

example : PALForm Ag := Formula.Box (Sum.inl a) (⌈Sum.inr (PA.Bang ⊤)⌉ ⊤)

notation:10000 "!!" n  => PA.Bang (Sum.inr n)

notation "K" => Formula.Box ∘ Sum.inl

-- example : Formula (PAL Ag) := K a (⌈!! ⊤⌉ ⊤) -- kaputt


-- (6) Dynamic Epistemic Logic with Action Models

structure ActM α where
  A : Type
  rel : α → A → A → Prop
  pre : ℕ → EpForm α -- pre-conditions can use `K`, but no ActM.

-- similar to PALForm, here we want boxes for both agents and ActM values
def DELForm (α : Type) := α ⊕ ActM α
