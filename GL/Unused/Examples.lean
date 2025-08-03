import GL.Unused.Basics
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const

universe u

namespace CategoryTheory

/- PRELIMINARIES -/

/- TODO: extend to all categories not just `Type u` -/
/- TODO: Think about type universes more than just putting `Type u` everywhere -/

def const : Type u → (Type u ⥤ Type u) :=
  λ C ↦ ⟨⟨λ x ↦ C, by aesop_cat⟩, by aesop_cat, by aesop_cat⟩

def id : (Type u ⥤ Type u) :=
  ⟨⟨λ x ↦ x, by aesop_cat⟩, by aesop_cat, by aesop_cat⟩

def const_id : Type u → (Type u ⥤ Type u) :=
  λ C ↦ ⟨⟨λ x ↦ C × x, by aesop_cat⟩, by aesop_cat, by aesop_cat⟩

/- EXAMPLE 1: Simple Black Box -/

/-
A set S of states not visible to the user along with a data set C of outputs combined with two maps
h and n where h which displays the output of a given state, and n which moves to the next state.
-/

structure simpleBlackBox (S C : Type u) where
  h : S → C
  n : S → S

instance {S C : Type u} (bb : simpleBlackBox S C) : System (const_id C) where
  X := S
  ξ := λ s ↦ ⟨bb.1 s, bb.2 s⟩


/- EXAMPLE 2: Streams -/

/- The streams over a type C is a map from ℕ to the type -/
/- FIXME : I think that the wording is wrong in the book -/

instance StreamSystem (C : Type u) : Coalgebra (const_id C) where
  X := ℕ → C
  ξ := λ α ↦ ⟨α 0, λ n ↦ α (n + 1)⟩
