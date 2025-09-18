import Mathlib.Data.Finset.Basic

/- Modal μ-calculus -/

namespace straightforward
inductive MuForm : (bs : List Nat) → Type
    | top {bs} : MuForm bs
    | bot {bs} : MuForm bs
    | at {bs} : Nat → MuForm bs
    | na {bs} : (x : Nat) → (x ∉ bs) → MuForm bs
    | and {bs} : MuForm bs → MuForm bs → MuForm bs
    | or {bs} : MuForm bs → MuForm bs → MuForm bs
    | box {bs} : MuForm bs → MuForm bs
    | dia {bs} : MuForm bs → MuForm bs
    | mu {bs} : (x : Nat) → MuForm (x :: bs) → MuForm bs
    | nu {bs} : (x : Nat) → MuForm (x :: bs) → MuForm bs

abbrev TrueMuForm := MuForm []

example : TrueMuForm := .mu 0 (.box (.at 0))
example : TrueMuForm := .mu 0 (.box (.na 0 (by sorry))) -- not possible!

end straightforward
-- In this case, the "true" μ-formulas are of type MuForm [], emphasis on the [].
-- What if want it to be all one type and not have TrueMuForm

namespace alternate
mutual
  inductive MuForm
    | top : MuForm
    | bot : MuForm
    | at : Nat → MuForm
    | na : Nat → MuForm
    | and : MuForm → MuForm → MuForm
    | or : MuForm → MuForm → MuForm
    | box : MuForm → MuForm
    | dia : MuForm → MuForm
    | mu : (x : Nat) → PosForm {x} → MuForm
    | nu : (x : Nat) → PosForm {x} → MuForm
  inductive PosForm : (P : Finset Nat) → Type
    | top {P} : PosForm P
    | bot {P} : PosForm P
    | at {P} : (n : Nat) → PosForm P
    | na {P} : (n : Nat) → (n ∉ P) → PosForm P
    | and {P} : PosForm P → PosForm P → PosForm P
    | or {P} : PosForm P → PosForm P → PosForm P
    | box {P} : PosForm P → PosForm P
    | dia {P} : PosForm P → PosForm P
    | mu {P} : (x : Nat) → PosForm (P ∪ {x}) → PosForm P
    | nu {P} : (x : Nat) → PosForm (P ∪ {x}) → PosForm P
end

example : MuForm := .mu 0 (.box (.at 0))
example : MuForm := .mu 0 (.box (.na 0 (by sorry))) -- not possible!

end alternate

-- Now we don't need the abbreviation!

/- Alternation free modal μ-calculus -/

namespace straightforward
inductive AFMuForm : (ms : Finset Nat) → (ns : Finset Nat) → Type
  | top {ms} {ns} : AFMuForm ms ns
  | bot {ms} {ns} : AFMuForm ms ns
  | at {ms} {ns} : Nat → AFMuForm ms ns
  | na {ms} {ns} : (x : Nat) → (x ∉ ns ∪ ms) → AFMuForm ms ns
  | or {ms} {ns} : AFMuForm ms ns → AFMuForm ms ns → AFMuForm ms ns
  | and {ms} {ns} : AFMuForm ms ns → AFMuForm ms ns → AFMuForm ms ns
  | box {ms} {ns} : AFMuForm ms ns → AFMuForm ms ns
  | dia {ms} {ns} : AFMuForm ms ns → AFMuForm ms ns
  | mu {ms} {ns} : (x : Nat) → (x ∉ ns) → AFMuForm ({x} ∪ ms) ns → AFMuForm ms ns
  | nu {ms} {ns} : (x : Nat) → (x ∉ ms) → AFMuForm ms ({x} ∪ ns) → AFMuForm ms ns

abbrev TrueAFMuForm := AFMuForm {} {}


example : TrueAFMuForm := .mu 0 (by simp) (.box (.at 0)) -- μx.□x
example : TrueAFMuForm := .mu 0 (by simp) (.box (.na 0 (by sorry))) -- μx.□¬x: not possible!
example : TrueAFMuForm := .and (.mu 0 (by simp) (.box (.at 0))) (.nu 0 (by simp) (.box (.at 0)) ) -- μx.□x ∧ vx.□x
example : TrueAFMuForm := .mu 0 (by simp) (.nu 1 (by simp) (.box (.at 1))) -- μx.vy.□y: possible!
example : TrueAFMuForm := .mu 0 (by simp) (.mu 1 (by simp) (.at 0)) -- μx.μy.x
example : TrueAFMuForm := .mu 0 (by simp) (.nu 1 (by simp) (.or (.at 0) (.at 1))) -- μx.νy.(x ∨ y)
end straightforward
-- something is wrong but I am close to understanding...

-- A neat version (but very long) version below

namespace alternate
mutual
  inductive AFMuForm
    | top : AFMuForm
    | bot : AFMuForm
    | at : Nat → AFMuForm
    | na : Nat → AFMuForm
    | and : AFMuForm → AFMuForm → AFMuForm
    | or : AFMuForm → AFMuForm → AFMuForm
    | box : AFMuForm → AFMuForm
    | dia : AFMuForm → AFMuForm
    | mu : (x : Nat) → PosMu {x} → AFMuForm
    | nu : (x : Nat) → PosNu {x} → AFMuForm
  inductive PosMu : (P : Finset Nat) → Type
    | top {P} : PosMu P
    | bot {P} : PosMu P
    | at {P} : (n : Nat) → PosMu P
    | na {P} : (n : Nat) → (n ∉ P) → PosMu P -- no negative occurences allowed in Noeth Fragment
    | and {P} : PosMu P → PosMu P → PosMu P
    | or {P} : PosMu P → PosMu P → PosMu P
    | box {P} : PosMu P → PosMu P
    | dia {P} : PosMu P → PosMu P
    | mu {P} : (x : Nat) → PosMu (P ∪ {x}) → PosMu P -- no ν-form allowed!!
  inductive PosNu : (P : Finset Nat) → Type
    | top {P} : PosNu P
    | bot {P} : PosNu P
    | at {P} : (n : Nat) → PosNu P
    | na {P} : (n : Nat) → (n ∉ P) → PosNu P -- no negative occurences allowed in Noeth Fragment
    | and {P} : PosNu P → PosNu P → PosNu P
    | or {P} : PosNu P → PosNu P → PosNu P
    | box {P} : PosNu P → PosNu P
    | dia {P} : PosNu P → PosNu P
    | nu {P} : (x : Nat) → PosNu (P ∪ {x}) → PosNu P -- no μ-form allowed!!
end
end alternate
