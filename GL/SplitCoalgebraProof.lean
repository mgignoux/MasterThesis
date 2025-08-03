import GL.CoalgebraProof

universe u

structure SplitInfiniteProof (Γ : Finset (Formula ⊕ Formula)) where
  X : Type u
  α : X → (T Γ).obj X
  x : X
-- r
-- h

def SplitInfiniteProof.Interpolant {Γ} (𝕏 : SplitInfiniteProof Γ) (h : Finite 𝕏.X) : Formula := by sorry



-- every SplitInfiniteProof can become an infinite proof
-- also it should be clear that every infinite proof can become a SplitInfiniteProof
