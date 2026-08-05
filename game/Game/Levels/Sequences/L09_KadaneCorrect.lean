import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 9
Title "Kadane Correctness"
-- source: RequestProject Lab09.kadane_isGreatest

Introduction "**Postcondition of Kadane's algorithm.** `kadane l` is the
greatest sum over all contiguous subarrays of `l`: it is one of those
sums, and it is `≥` every one of them. Assemble it from the supplied
witness and upper-bound cards."

Statement (l : List ℤ) : IsGreatest (subSums l) (kadane l) := by
  Hint "`IsGreatest` needs membership (a witness block attaining the value)
  and an upper bound over every block."
  refine ⟨?_, fun x hx => ?_⟩
  · Hint (hidden := true) "The witness comes from `maxSubSum_mem`, transported through
    `kadane_eq`."
    obtain ⟨i, j, h⟩ := maxSubSum_mem l
    exact ⟨i, j, by linarith [kadane_eq l]⟩
  · Hint (hidden := true) "Destructure the block witness, then combine `maxSubSum_ub` with
    `kadane_eq`."
    obtain ⟨i, j, rfl⟩ := hx
    exact by linarith [maxSubSum_ub l i j, kadane_eq l]

Conclusion "Verified: Kadane's algorithm provably finds the greatest subarray sum."

NewDefinition Game.Design.subSums
NewTheorem Game.Design.maxSubSum_mem Game.Design.maxSubSum_ub Game.Design.kadane_eq
