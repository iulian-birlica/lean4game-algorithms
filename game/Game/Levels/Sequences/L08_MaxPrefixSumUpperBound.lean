import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 8
Title "Max Prefix Sum Upper Bound"
-- source: RequestProject Lab09.maxPrefixSum_ub

Introduction "`maxPrefixSum` should really be the *largest* prefix sum.
Prove the upper-bound half: every prefix's sum is at most `maxPrefixSum`."

Statement (l : List ℤ) (j : ℕ) : (l.take j).sum ≤ maxPrefixSum l := by
  Hint "Induct on `l`, generalizing `j`; case on whether `j` is `0` or a
  successor."
  induction' l with x l ih generalizing j
  · cases j <;> trivial
  · Hint (hidden := true) "`rcases j with (_|j) <;> simp [maxPrefixSum]`."
    rcases j with (_ | j) <;> simp_all +decide [maxPrefixSum]

Conclusion "Verified: no prefix beats `maxPrefixSum`."

NewTactic trivial
NewTheorem List.sum_nil List.sum_cons List.take_succ_cons
