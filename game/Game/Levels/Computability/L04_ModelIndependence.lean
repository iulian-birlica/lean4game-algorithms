import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 4
Title "Model Independence"
-- source: RequestProject Lab21.model_independence

Introduction "Undecidability is a property of computation itself, not of a particular
formalism. Mathlib's tape-based Turing-machine model and the code model compute exactly the
same partial functions. Record the code-side direction: a function is `Nat.Partrec` iff it is
the behaviour `eval c` of some program code `c` — the sense in which the two models coincide."

Statement (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∃ c : Nat.Partrec.Code, c.eval = f := by
  Hint "This equivalence is exactly Mathlib's own witness that the code model computes precisely
  the partial-recursive functions."
  exact Nat.Partrec.Code.exists_code

Conclusion "Verified: the code model and the partial-recursive (equivalently, Turing-machine)
model compute exactly the same functions."

NewDefinition Nat.Partrec Nat.Partrec.Code.eval
NewTheorem Nat.Partrec.Code.exists_code
