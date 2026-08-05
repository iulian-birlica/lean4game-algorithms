import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Recurrence"
Level 1
Title "Recurrence Unrolling"
-- source: RequestProject Lab11.masterSeq_closed

Introduction "A divide-and-conquer recurrence `Tₖ = a·T_{k-1} + Fₖ` (with
`T₀ = d`) unrolls into a closed form: `aᵏ` copies of the base cost, plus one
weighted toll per level. Prove the unrolling."

Statement (a d : ℝ) (F : ℕ → ℝ) (k : ℕ) :
    masterSeq a d F k = a ^ k * d + ∑ i ∈ Finset.range k, a ^ i * F (k - i) := by
  Hint "Induct on `k`; the base case unfolds directly, the step needs
  `Finset.sum_range_succ'` to peel off the new level."
  induction' k with k ih
  · norm_num [masterSeq]
  · Hint (hidden := true) "`rw [Finset.sum_range_succ', masterSeq]`, then `simp_all` with the
    ring-normal-form lemmas."
    rw [Finset.sum_range_succ', masterSeq]
    simp_all +decide only [mul_add, Finset.mul_sum _ _ _, add_assoc, pow_succ', mul_assoc,
      Nat.reduceSubDiff, pow_zero, tsub_zero, one_mul]

Conclusion "Unrolled: the recurrence has an explicit closed form."

NewDefinition Game.Clockwork.masterSeq
NewTheorem Finset.sum_range_succ' mul_add Finset.mul_sum add_assoc pow_succ' pow_succ
  Nat.reduceSubDiff tsub_zero
