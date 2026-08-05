import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L04_InsertSortedHead

open Game.Clockwork

World "InsertionSort"
Level 5
Title "Sortedness: Recursive Branch"

Introduction "Now the other branch: when `¬ x ≤ y`, `insert` keeps `y` at the
front and recurses into the tail. Assuming the recursive call `insert x ys` is
already sorted (`ihp`), show `y :: insert x ys` is sorted. The new head
condition — that `y` bounds everything in `insert x ys` — is exactly the
lower-bound invariant from Level 2."

/-- Sortedness step, second branch (`¬ x ≤ y`): the old head is kept. -/
Statement insert_sorted_tail (x y : ℕ) (ys : List ℕ)
    (hxy : ¬ x ≤ y) (hs : (y :: ys).Pairwise (· ≤ ·))
    (ihp : (Game.Clockwork.insert x ys).Pairwise (· ≤ ·)) :
    (y :: Game.Clockwork.insert x ys).Pairwise (· ≤ ·) := by
  Hint "Destructure `hs`, simplify with `List.pairwise_cons`, and supply the head
  bound with `insert_lower_bound`."
  obtain ⟨hy, htail⟩ := List.pairwise_cons.mp hs
  simp only [List.pairwise_cons]
  exact ⟨insert_lower_bound y x ys (le_of_lt (not_le.mp hxy)) hy, ihp⟩

Conclusion "The recursive branch of the step is ready."

NewTactic obtain simp exact
NewTheorem List.pairwise_cons insert_lower_bound le_of_lt not_le insert_sorted_tail
