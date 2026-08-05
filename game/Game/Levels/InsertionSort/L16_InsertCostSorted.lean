import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L15_InsertCost

open Game.Clockwork

World "InsertionSort"
Level 16
Title "Cost of Inserting Into a Sorted Tail"

Introduction "For the quadratic bound we need each insertion's cost measured
against the *original* tail length. Combine the per-insertion bound from Level 15
with length preservation from Level 13: inserting into an already-sorted tail
costs at most the original tail's length."

/-- Inserting into a sorted tail costs at most the original tail's length. -/
Statement insertCost_insertionSort_le (x : ℕ) (xs : List ℕ) :
    Game.Clockwork.insertCost x (insertionSort xs) ≤ xs.length := by
  Hint "Chain `insertCost_le_length` with `insertionSort_length` using `calc`."
  calc Game.Clockwork.insertCost x (insertionSort xs)
        ≤ (insertionSort xs).length := insertCost_le_length _ _
    _ = xs.length := insertionSort_length xs

Conclusion "The per-step cost is now expressed in the original tail's length."

NewTheorem insertCost_le_length insertionSort_length insertCost_insertionSort_le
