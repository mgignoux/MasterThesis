import GL.Logic
import GL.CoalgebraProof
import GL.SplitCoalgebraProof

/- SYSTEMS OF EQUATIONS -/

/- Structure preserving map substituting Pₙ by C -/
def single (n : Nat) (C : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at k => if k == n then C else at k
  | na k => if k == n then ~ C else na k
  | A & B => (single n C A) & (single n C B)
  | A v B => (single n C A) v (single n C B)
  | □ A => □ (single n C A)
  | ◇ A => ◇ (single n C A)

/- Structure preserving map substituting all atoms meeting a certain criteria p -/
def partial_ (p : Nat → Prop) [DecidablePred p] (σ : Subtype p → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : p n then σ ⟨n, h⟩ else at n
  | na n => if h : p n then ~ σ ⟨n, h⟩ else at n
  | A & B => (partial_ p σ A) & (partial_ p σ B)
  | A v B => (partial_ p σ A) v (partial_ p σ B)
  | □ A => □ (partial_ p σ A)
  | ◇ A => ◇ (partial_ p σ A)

/- Structure preserving map substituting all atoms via a transformation σ -/
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

/- Shift all atoms up or down, might come in handy later -/
def shift_up (k : Nat) : Formula → Formula := full (λ n ↦ at (n + k))
def shift_down (k : Nat) : Formula → Formula := full (λ n ↦ at (n - k))

namespace split

def equation (𝕏 : GLSplitProof) {n : Nat} (bij : 𝕏.X ≃ Fin n) (x : 𝕏.X) : Formula := match r 𝕏.α x with
  | RuleApp.topₗ => ⊥
  | RuleApp.topᵣ => ⊤
  | RuleApp.axₗₗ _ => ⊥
  | RuleApp.axₗᵣ k => na (k + n) -- probably shift this up by n to avoid issues later
  | RuleApp.axᵣₗ k => at (k + n)
  | RuleApp.axᵣᵣ _ => ⊤
  | RuleApp.orₗ A B => at (bij.toFun (by sorry))
  | RuleApp.orᵣ A B => by sorry
  | RuleApp.andₗ A B => by sorry
  | RuleApp.andᵣ A B => by sorry
  | RuleApp.boxₗ A => by sorry
  | RuleApp.boxᵣ A => by sorry
