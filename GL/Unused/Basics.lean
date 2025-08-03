import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const

universe u v w

namespace CategoryTheory

structure Coalgebra {C : Type u} [Category C] (T : C ⥤ C) where
  X : C
  ξ : X ⟶ T.obj X

structure CoalgebraMorphism {C : Type u} [Category C] {T : C ⥤ C} (𝕏 𝕏' : Coalgebra T) where
  f : 𝕏'.1 ⟶ 𝕏.1
  h : f ≫ 𝕏.2 = 𝕏'.2 ≫ (T.map f)

instance {C : Type u} [Category C] (T : C ⥤ C) : CategoryStruct (Coalgebra T) where
  Hom := CoalgebraMorphism
  id 𝕏 := ⟨𝟙 𝕏.1, by simp⟩
  comp f g := ⟨g.1 ≫ f.1, by
    rw [CategoryTheory.Category.assoc g.1 f.1 _, f.2,
       ←CategoryTheory.Category.assoc g.1 _ _, g.2]
    simp
    ⟩

instance CoAlg {C : Type u} [Category C] (T : C ⥤ C) : Category (Coalgebra T) where
  id_comp f := by simp only [CategoryStruct.comp, CategoryStruct.id, Category.comp_id]; rfl
  comp_id f := by simp only [CategoryStruct.comp, CategoryStruct.id, Category.id_comp]; rfl
  assoc f g h := by simp only [CategoryStruct.comp, Category.assoc]

/-
structure System (T : Set ⥤ Set) :=
  X : Set
  ξ : Set ⟶ T.obj Set

This is not possible, because there is no category Set or instance for a category
of Sets in Lean. Instead we use `Type` (see for instance how the Yoneda embedding
is defined in Lean) using `Type`.
-/

structure System (T : Type v ⥤ Type v) extends Coalgebra T

/-
Using this definition, it is possible to define a pointed system, where instead
of using c ∈ X where X ∈ "The objects of the category Set", we now have c : X,
where X : Type u.
-/

structure PointedSystem (T : Type v ⥤ Type v) extends System T where
  c : X
