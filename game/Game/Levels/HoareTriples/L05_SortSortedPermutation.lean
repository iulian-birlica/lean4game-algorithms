import Game.Metadata
import Game.Support.Contracts

World "HoareTriples"
Level 5
Title "Sort Gives a Sorted Permutation"
-- source: RequestProject Lab01.sort_spec (ported from game W01-L05)

Introduction "Prove that the foundry's `sort` routine produces a sorted
permutation of its input."

Statement (values : List Int) :
    Game.Contracts.IsSorted (Game.Contracts.sort values) ∧
      (Game.Contracts.sort values).Perm values := by
  Hint "Use the merge-sort permutation and pairwise-sortedness cards."
  unfold Game.Contracts.IsSorted Game.Contracts.sort
  refine ⟨?_, List.mergeSort_perm values _⟩
  Hint (hidden := true) "The comparator facts follow from transitivity and totality of `≤` on `Int`."
  have h := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc =>
      decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by
      rcases le_total a b with hle | hle
      · exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hle))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true hle))) values
  exact h.imp (fun hab => of_decide_eq_true hab)

Conclusion "Output verified: sorted, and nothing lost or added."

NewTactic «have» rcases
NewDefinition Game.Contracts.IsSorted Game.Contracts.sort Or.inl Or.inr Decidable.decide
NewTheorem List.mergeSort_perm List.pairwise_mergeSort le_total le_trans
  decide_eq_true of_decide_eq_true Bool.or_eq_true_iff
