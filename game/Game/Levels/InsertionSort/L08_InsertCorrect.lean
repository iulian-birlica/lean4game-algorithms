import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L07_InsertSorted

open Game.Clockwork

World "InsertionSort"
Level 8
Title "Insertion Correctness"

Introduction "Combine the two main helper results: insertion preserves all
elements and insertion into a sorted list remains sorted."

/-- Full functional correctness for inserting one element. -/
Statement insert_correct (x : ℕ) (s : List ℕ) (hs : s.Pairwise (· ≤ ·)) :
    List.Perm (Game.Clockwork.insert x s) (x :: s) ∧ (Game.Clockwork.insert x s).Pairwise (· ≤ ·) := by
  Hint "Each conjunct is a theorem from an earlier level."
  exact ⟨insert_perm x s, insert_sorted x s hs⟩

Conclusion "The insertion helper is correct."

NewTactic exact
NewTheorem insert_perm insert_sorted insert_correct
