import Game.Metadata
import Game.Support.Contracts

World "HoareTripleExercises"
Level 2
Title "Bubble Pass Length and Permutation"
-- source: RequestProject Lab04.bubblePass_length, Lab04.bubblePass_perm

Introduction "One pass of `bubblePass` performs adjacent compare-swaps.
Prove its two basic invariants: a pass never changes the length, and it
only rearranges elements. `induction ... using bubblePass.induct` hands
you exactly one case per branch of the definition."

Statement (l : List Int) :
    (Game.Contracts.bubblePass l).length = l.length ∧ (Game.Contracts.bubblePass l).Perm l := by
  Hint "Prove the two facts separately, each by `induction l using bubblePass.induct with`."
  constructor
  · induction l using Game.Contracts.bubblePass.induct with
    | case1 => rw [Game.Contracts.bubblePass]
    | case2 x => rw [Game.Contracts.bubblePass]
    | case3 x y rest hxy ih =>
      rw [Game.Contracts.bubblePass, if_pos hxy]; simp only [List.length_cons, ih]
    | case4 x y rest hxy ih =>
      rw [Game.Contracts.bubblePass, if_neg hxy]; simp only [List.length_cons, ih]
  · induction l using Game.Contracts.bubblePass.induct with
    | case1 => rw [Game.Contracts.bubblePass]
    | case2 x => rw [Game.Contracts.bubblePass]
    | case3 x y rest hxy ih =>
      Hint (hidden := true) "When `x ≤ y`, the pass keeps `x` in front and permutes the
      tail by the induction hypothesis."
      rw [Game.Contracts.bubblePass, if_pos hxy]; exact ih.cons x
    | case4 x y rest hxy ih =>
      Hint (hidden := true) "When `y < x`, `x` and `y` are swapped, then the tail is
      permuted by the induction hypothesis."
      rw [Game.Contracts.bubblePass, if_neg hxy]
      exact (ih.cons y).trans (List.Perm.swap x y rest)

Conclusion "Verified: a bubble pass preserves length and only rearranges elements."

NewDefinition Game.Contracts.bubblePass Game.Contracts.bubblePass.induct
NewTheorem List.Perm.swap
