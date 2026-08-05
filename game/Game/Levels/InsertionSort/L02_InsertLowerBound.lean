import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L01_InsertPerm

open Game.Clockwork

World "InsertionSort"
Level 2
Title "A Lower-Bound Invariant"

Introduction "If `y` is below the new element and every old element, then it
is below every element returned by `Game.Clockwork.insert`. Use the permutation result from
Level 1 rather than repeating the recursion."

/-- A common lower bound is preserved by insertion. -/
Statement insert_lower_bound (y x : ℕ) (s : List ℕ)
    (hyx : y ≤ x) (hys : ∀ a ∈ s, y ≤ a) :
    ∀ a ∈ Game.Clockwork.insert x s, y ≤ a := by
  intro a ha
  Hint "Transport membership through `insert_perm`."
  have h_mem : a ∈ x :: s := List.Perm.subset (insert_perm x s) ha
  rcases List.mem_cons.mp h_mem with rfl | ha
  · exact hyx
  · exact hys a ha

Conclusion "The lower-bound invariant is ready for the sortedness proof."

NewTactic intro rcases exact rfl
NewTheorem insert_perm List.Perm.subset List.mem_cons insert_lower_bound
