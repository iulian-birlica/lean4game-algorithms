import Game.Metadata
import Game.Support.Contracts

World "HoareTriples"
Level 6
Title "Binary Search Membership"
-- source: RequestProject Lab01.binarySearch_spec (ported from game W01-L06, boss level)

Introduction "The public binary-search routine must agree with membership in
the array — for every sorted array and every target. Derive it from the
supplied interval invariant."

Statement (a : Array Int) (target : Int) (hsorted : Game.Contracts.IsSortedArr a) :
    Game.Contracts.binarySearch a target = true ↔ target ∈ a.toList := by
  Hint "Rewrite the public routine with the interval invariant over the whole array."
  rw [Game.Contracts.binarySearch,
    Game.Contracts.binarySearchAux_spec a target hsorted 0 a.size (le_refl _),
    Array.mem_toList_iff, Array.mem_iff_getElem]
  Hint (hidden := true) "Translate the index witness in both directions."
  constructor
  · rintro ⟨i, hisz, _, _, hai⟩
    exact ⟨i, hisz, hai⟩
  · rintro ⟨i, hisz, hai⟩
    exact ⟨i, hisz, Nat.zero_le _, hisz, hai⟩

Conclusion "The vault opens: binary search agrees with membership, always."

NewTactic rintro
NewDefinition Game.Contracts.binarySearch
NewTheorem Game.Contracts.binarySearchAux_spec Array.mem_toList_iff Array.mem_iff_getElem Nat.zero_le le_refl
