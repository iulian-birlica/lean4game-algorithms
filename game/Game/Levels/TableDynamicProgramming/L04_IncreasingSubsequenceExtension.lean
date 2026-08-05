import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 4
Title "Increasing-Subsequence Extension"

Introduction "For longest increasing subsequence, a candidate remains strictly
increasing when you append a new final value that is larger than every old
entry. Split the appended list into the old candidate and the singleton tail."

/-- Appending a larger final value preserves strict increase. -/
Statement (xs : List Nat) (x : Nat)
    (hincreasing : StrictlyIncreasing xs)
    (hbelow : ∀ y ∈ xs, y < x) :
    StrictlyIncreasing (xs ++ [x]) := by
  Hint "Unfold `StrictlyIncreasing`, rewrite `Pairwise` over append, and prove
  every old element is below the new singleton element."
  unfold StrictlyIncreasing at hincreasing ⊢
  rw [List.pairwise_append]
  refine ⟨hincreasing, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  exact hbelow a ha

Conclusion "The LIS candidate can be extended by a value above all previous entries."

NewTactic exact intro refine rw simp subst unfold
NewDefinition Game.TableDP.StrictlyIncreasing
NewTheorem List.pairwise_append List.mem_singleton
