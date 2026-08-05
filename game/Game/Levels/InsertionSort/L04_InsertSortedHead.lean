import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L03_InsertSortedBase

open Game.Clockwork

World "InsertionSort"
Level 4
Title "Sortedness: New-Head Branch"

Introduction "The inductive step of the sortedness proof splits on how
`Game.Clockwork.insert` behaves. Handle the first branch here: when
`x ≤ y`, `insert` puts `x` at the front, so we must show `x :: y :: ys` is
sorted. Because `x ≤ y` and `y` already bounds the tail, `x` bounds the whole
list, and `y :: ys` was sorted to begin with."

/-- Sortedness step, first branch (`x ≤ y`): the new element becomes the head. -/
Statement insert_sorted_head (x y : ℕ) (ys : List ℕ)
    (hxy : x ≤ y) (hs : (y :: ys).Pairwise (· ≤ ·)) :
    (x :: y :: ys).Pairwise (· ≤ ·) := by
  Hint "Destructure `hs`, simplify with `List.pairwise_cons`, and discharge the
  new head bounds using `le_trans`."
  obtain ⟨hy, htail⟩ := List.pairwise_cons.mp hs
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
  exact ⟨⟨hxy, fun a ha => le_trans hxy (hy a ha)⟩, hy, htail⟩

Conclusion "The `x ≤ y` branch of the step is ready."

NewTactic obtain simp exact
NewTheorem List.pairwise_cons List.mem_cons le_trans insert_sorted_head
