import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L11_InsertionSortCorrect

open Game.Clockwork

World "InsertionSort"
Level 12
Title "Insertion Adds One Element"

Introduction "Correctness is done; now analyse the algorithm's shape and cost.
Start with the simplest structural fact: inserting an element makes the list
exactly one longer."

/-- Insertion increases the length of the list by exactly one. -/
Statement insert_length (x : ℕ) (s : List ℕ) :
    (Game.Clockwork.insert x s).length = s.length + 1 := by
  Hint "Induct on `s`, unfold `Game.Clockwork.insert`, and split on its comparison."
  induction' s with y ys ih
  · rfl
  · simp only [Game.Clockwork.insert]
    split
    · rfl
    · simp [ih]

Conclusion "Insertion adds exactly one element."

NewTactic induction' simp split rfl
NewTheorem insert_length
