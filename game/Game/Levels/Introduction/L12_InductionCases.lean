import Game.Metadata

World "Intro"
Level 12
Title "Induction Cases"

Introduction "Induction on a natural number opens exactly two cases:
the base case `0`, and the successor case `Nat.succ k`.
In the successor case Lean also gives you an induction hypothesis for `k`."

Statement : ∀ n : ℕ, n + 0 = n := by
  intro n
  Hint "Induct on `{n}`."
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      Hint (hidden := true) "This successor case closes by computation, so you do not need `{ih}` yet."
      rfl

Conclusion "An induction proof always checks the zero case and the successor case."

NewTactic induction
OnlyTactic intro induction rfl
