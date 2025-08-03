import GL.Logic
import GL.CoalgebraProof

unsafe def graphviz_single {Γ : Finset Formula} {𝕏 : InfiniteProof Γ} (x : 𝕏.1) (y : 𝕏.1)
  := "\"" ++ pp_forms (f 𝕏.α x) ++ "\" -> \"" ++ pp_forms (f 𝕏.α y) ++ "\"[label=\"" ++ labelPrint (fₚ 𝕏.α x) ++ "\"] ; \n"

unsafe def graphviz_print_rec {Γ : Finset Formula} (𝕏 : InfiniteProof Γ) (x : 𝕏.1) (n : ℕ) (output : List String) : String :=
match n with
  | 0 => ""
  | n + 1 =>
    match Quot.unquot (p 𝕏.α x) with
      | [] => ""
      | y :: [] => if graphviz_single x y ∈ output then "" else graphviz_single x y ++ graphviz_print_rec 𝕏 y n (graphviz_single x y :: output)
      | y :: z :: [] => if graphviz_single x y ∈ output
                        then (if graphviz_single x z ∈ output then "" else graphviz_single x z ++ graphviz_print_rec 𝕏 y n (graphviz_single x z :: output))
                        else (if graphviz_single x z ∈ output then (graphviz_single x y ++ graphviz_print_rec 𝕏 y n (graphviz_single x y :: output))
                              else graphviz_single x y ++ graphviz_single x z ++ graphviz_print_rec 𝕏 y n (graphviz_single x y :: graphviz_single x z :: output))
      | _ => ""

def Γ : Finset Formula := {◇ (□ P ∧ᴳ (¬ᴳ P)) ∨ᴳ □ (¬ᴳ P), ◇ (□ P ∧ᴳ (¬ᴳ P)), □ (¬ᴳ P), (□ P ∧ᴳ (¬ᴳ P)), □ P, ¬ᴳ P, P}

instance GLAxPf : InfiniteProof Γ where
  X := { x : String // x = "1" ∨ x = "11" ∨ x = "111" ∨ x = "1111" ∨ x = "1112" ∨ x = "11111" }
  x := ⟨"1", by simp⟩
  α := λ x ↦ if x = "1"     then ⟨⟨{◇ (□ P ∧ᴳ (¬ᴳ P)) ∨ᴳ □ (¬ᴳ P)}, by decide⟩, ⟨{}, by simp⟩, {⟨"11", by simp⟩}⟩
        else if x = "11"    then ⟨⟨{□ (¬ᴳ P)}, by decide⟩,                      ⟨{◇ (□ P ∧ᴳ (¬ᴳ P))}, by decide⟩,    {⟨"111", by simp⟩}⟩
        else if x = "111"   then ⟨⟨{□ P ∧ᴳ (¬ᴳ P)}, by decide⟩,                 ⟨{◇ (□ P ∧ᴳ (¬ᴳ P)), P}, by decide⟩, {⟨"1111", by simp⟩, ⟨"1112", by simp⟩}⟩
        else if x = "1111"  then ⟨⟨{□ P}, by decide⟩,                           ⟨{◇ (□ P ∧ᴳ (¬ᴳ P)), P}, by decide⟩, {⟨"111", by simp⟩}⟩
        else if x = "1112"  then ⟨⟨{¬ᴳ P, P}, by decide⟩,                       ⟨{◇ (□ P ∧ᴳ (¬ᴳ P))}, by decide⟩,    {}⟩
        else ⟨⟨{}, by simp⟩, ⟨{}, by decide⟩, {}⟩
  r := by sorry
  h := by sorry
    -- intro ⟨x, x_cases⟩
    -- rcases x_cases with x_def | x_def | x_def | x_def | x_def | x_def <;> subst x_def
    -- · apply Or.inr
    --   apply Or.inr
    --   apply Or.inr
    --   apply Or.inl
    --   simp [fₚ, p, f, fₙ]




#eval! IO.println (graphviz_print_rec GLAxPf ⟨"1", by simp⟩ 5 [])

-- graphviz
-- rubiks cube visualization
-- modify PDL haskell prover
