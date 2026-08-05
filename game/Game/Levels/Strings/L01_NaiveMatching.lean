import Game.Metadata
import Game.Support.Design

open Game.Design

World "Strings"
Level 1
Title "Naive Matching"
-- source: RequestProject Lab10.mem_naiveMatches

Introduction "The naive string matcher tries every candidate position and
compares directly. Prove it returns exactly the positions where the
pattern actually matches."

Statement (text pat : List ℕ) (i : ℕ) :
    i ∈ naiveMatches text pat ↔ i ≤ text.length ∧ matchAt text pat i := by
  Hint "Unfold `naiveMatches` and `matchAt`, then simplify membership in a
  filtered range."
  unfold naiveMatches matchAt
  Hint (hidden := true) "`rw [List.mem_filter, List.mem_range, Nat.lt_add_one_iff,
  decide_eq_true_eq]`."
  rw [List.mem_filter, List.mem_range, Nat.lt_add_one_iff, decide_eq_true_eq]

Conclusion "Verified: the naive matcher finds exactly the true matches."

NewDefinition Game.Design.naiveMatches Game.Design.matchAt
NewTheorem List.mem_filter List.mem_range Nat.lt_add_one_iff decide_eq_true_eq
