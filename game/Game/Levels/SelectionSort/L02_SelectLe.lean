import Game.Metadata
import Game.Support.SelectionSort
import Game.Levels.SelectionSort.L01_SelectPerm

open Game.Clockwork

World "SelectionSort"
Level 2
Title "The Selected Element Bounds the Candidate"

Introduction "The element `select` returns can only get smaller than the
candidate you start with. Prove that the extracted minimum is at most `x`."

/-- The minimum `select` extracts is `≤` the starting candidate. -/
Statement select_le (x : ℕ) (s : List ℕ) : (select x s).1 ≤ x := by
  Hint "Induct on `s` (generalizing `x`) and split on the comparison. In the
  `¬ x ≤ y` branch, combine the induction hypothesis with `not_le`."
  induction s generalizing x with
  | nil => simp [select]
  | cons y ys ih =>
    simp only [select]
    split <;> rename_i h
    · exact ih x
    · exact le_trans (ih y) (le_of_lt (not_le.mp h))

Conclusion "The extracted element never exceeds the starting candidate."

NewTactic induction simp split rename_i exact
NewTheorem le_trans le_of_lt not_le select_le
