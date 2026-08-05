import Game.Metadata
import Game.Support.SelectionSort
import Game.Levels.SelectionSort.L02_SelectLe

open Game.Clockwork

World "SelectionSort"
Level 3
Title "The Selected Element Is Minimal"

Introduction "Now prove that `select` really does extract a minimum: the element
it returns is `≤` every leftover element. Use `select_le` from the previous
level to handle the newly exposed head in each branch."

/-- The element `select` extracts is `≤` every leftover element. -/
Statement select_min (x : ℕ) (s : List ℕ) :
    ∀ a ∈ (select x s).2, (select x s).1 ≤ a := by
  Hint "Induct on `s` (generalizing `x`) and split on the comparison. After
  `List.mem_cons`, the new head is bounded via `select_le` and the rest via the
  induction hypothesis."
  induction s generalizing x with
  | nil => simp [select]
  | cons y ys ih =>
    simp only [select]
    split <;> rename_i h
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_trans (select_le x ys) h
      · exact ih x a ha
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_trans (select_le y ys) (le_of_lt (not_le.mp h))
      · exact ih y a ha

Conclusion "`select` extracts a genuine minimum of the list."

NewTactic induction simp split rename_i intro rcases exact
NewTheorem List.mem_cons le_trans le_of_lt not_le select_le select_min
