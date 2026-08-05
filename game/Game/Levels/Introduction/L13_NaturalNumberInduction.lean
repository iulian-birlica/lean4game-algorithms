import Game.Metadata

World "Intro"
Level 13
Title "Natural Number Induction"

Introduction "Now use the full induction pattern on a theorem where the
successor case really needs the induction hypothesis.
After rewriting `0 + Nat.succ k`, the fact already proved for `k` finishes the
step."

Statement : ∀ n : ℕ, 0 + n = n := by
  intro n
  Hint "Induct on `{n}`."
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      Hint (hidden := true) "Rewrite with `Nat.add_succ`, then use the induction hypothesis `{ih}`."
      rw [Nat.add_succ, ih]

Conclusion "The base case and the successor step together covered every natural number."

NewTheorem Nat.add_succ
OnlyTactic intro induction rfl rw
