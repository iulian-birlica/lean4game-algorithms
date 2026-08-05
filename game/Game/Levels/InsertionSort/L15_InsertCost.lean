import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L14_InsertionSortMem

open Game.Clockwork

World "InsertionSort"
Level 15
Title "Counting Comparisons"

Introduction "`Game.Clockwork.insertCost x s` counts the comparisons made
while inserting `x`: one per element inspected. Prove the fundamental cost bound:
inserting into a list of length `n` uses at most `n` comparisons."

/-- Inserting one element costs at most as many comparisons as the list is long. -/
Statement insertCost_le_length (x : ℕ) (s : List ℕ) :
    Game.Clockwork.insertCost x s ≤ s.length := by
  Hint "Induct on `s`, unfold `Game.Clockwork.insertCost`, split on the
  comparison, and finish each branch with `omega`."
  induction' s with y ys ih
  · simp [Game.Clockwork.insertCost]
  · simp only [Game.Clockwork.insertCost, List.length_cons]
    split
    · omega
    · omega

Conclusion "Each insertion costs at most a linear number of comparisons."

NewDefinition Game.Clockwork.insertCost
NewTactic induction' simp split omega
NewTheorem List.length_cons insertCost_le_length
