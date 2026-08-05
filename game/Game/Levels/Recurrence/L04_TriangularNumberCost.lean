import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Recurrence"
Level 3
Title "Triangular Number Cost"
-- source: RequestProject Lab12.tri_succ, Lab12.tri_closed

Introduction "With the Landau vocabulary and `TimeM` cost monad in hand, we
put them to work on four classic sorting algorithms. First, the triangular
number `tri n = 0 + 1 + … + (n-1)`, which will turn out to be selection
sort's exact comparison count. Prove its recurrence and closed form."

Statement (n : ℕ) : tri (n + 1) = tri n + n ∧ tri n = n * (n - 1) / 2 := by
  Hint "Prove the two facts separately."
  constructor
  · simp only [tri, Finset.sum_range_succ]
  · Hint (hidden := true) "`rw [Nat.div_eq_of_eq_mul_left zero_lt_two]`, then convert to
    `Finset.sum_range_id_mul_two`."
    rw [Nat.div_eq_of_eq_mul_left zero_lt_two]
    convert Finset.sum_range_id_mul_two n |> Eq.symm using 1

Conclusion "Ticked: the triangular clock has both a recurrence and a closed form."

NewDefinition Game.Clockwork.tri Game.Clockwork.size
NewTactic convert
NewTheorem Finset.sum_range_succ Nat.div_eq_of_eq_mul_left zero_lt_two
  Finset.sum_range_id_mul_two Eq.symm
