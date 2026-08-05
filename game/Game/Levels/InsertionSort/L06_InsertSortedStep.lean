import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L05_InsertSortedTail

open Game.Clockwork

World "InsertionSort"
Level 6
Title "Sortedness: Inductive Step"

Introduction "Assemble the inductive step. Assume, as the induction hypothesis
`ih`, that inserting `x` into the tail `ys` stays sorted, and show that inserting
`x` into `y :: ys` stays sorted. Unfold `Game.Clockwork.insert`, split on
the comparison, and hand each branch to the lemma from Level 4 or Level 5."

/-- Inductive step of the sortedness invariant. -/
Statement insert_sorted_cons (x y : ℕ) (ys : List ℕ)
    (hs : (y :: ys).Pairwise (· ≤ ·))
    (ih : ys.Pairwise (· ≤ ·) → (Game.Clockwork.insert x ys).Pairwise (· ≤ ·)) :
    (Game.Clockwork.insert x (y :: ys)).Pairwise (· ≤ ·) := by
  Hint "Unfold `insert`, `split` on the comparison, then call `insert_sorted_head`
  and `insert_sorted_tail`."
  simp only [Game.Clockwork.insert]
  split <;> rename_i hxy
  · exact insert_sorted_head x y ys hxy hs
  · exact insert_sorted_tail x y ys hxy hs (ih (List.pairwise_cons.mp hs).2)

Conclusion "The inductive step is ready to be dropped into the main induction."

NewTactic simp split rename_i exact
NewTheorem List.pairwise_cons insert_sorted_head insert_sorted_tail insert_sorted_cons
