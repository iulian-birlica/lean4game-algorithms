import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 4
Title "Partition to Sum"
-- source: RequestProject Lab19.partToSS_correct, Lab19.partition_reduces_subsetSum

Introduction "**Partition** asks whether a list can be split into two groups of equal sum;
**Subset-Sum** asks whether some sub-collection sums to a given target. Partition is the
special case of aiming at half the total (or an obvious no-instance, if the total is odd).
Prove answer preservation, then assemble the reduction."

Statement :
    (∀ w : List ℕ, PartitionProblem w ↔ SubsetSum (partToSS w)) ∧
    PolyReducible partSize ssSize PartitionProblem SubsetSum := by
  Hint "Case on whether the total is even. When it is, both directions of the target-sum
  equation are the same arithmetic fact up to `omega`; when it is odd, no split can exist."
  have hcorr : ∀ w : List ℕ, PartitionProblem w ↔ SubsetSum (partToSS w) := by
    intro w
    by_cases h : w.sum % 2 = 0 <;>
      simp_all +decide only [PartitionProblem, SubsetSum, partToSS, ↓reduceIte,
        Nat.mod_two_not_eq_zero, one_ne_zero, List.length_nil, List.length_eq_zero_iff,
        exists_eq_left, iff_false, not_exists, not_and]
    · constructor
      · rintro ⟨m, hlen, heq⟩; exact ⟨m, hlen, by omega⟩
      · rintro ⟨m, hlen, heq⟩; exact ⟨m, hlen, by omega⟩
    · intro x _ heq; omega
  refine ⟨hcorr, ?_⟩
  exact PolyReducible.of_map partToSS (fun m => 3 * (m + 1)) (IsPolyBounded.linear 3)
    hcorr partToSS_size

Conclusion "Verified: Partition reduces to Subset-Sum in polynomial time."

NewDefinition Game.Complexity.selSum Game.Complexity.PartitionProblem Game.Complexity.SubsetSumInst
  Game.Complexity.SubsetSum Game.Complexity.partToSS
NewTheorem Game.Complexity.partToSS_size one_ne_zero not_exists not_and Nat.mod_two_not_eq_zero
  List.length_eq_zero_iff iff_false exists_eq_left
