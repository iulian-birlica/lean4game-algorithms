import Game.Metadata
import Game.Support.SortBasics

open Game.Clockwork

World "ComparisonSorts"
Level 1
Title "A Sorted Permutation Is Unique"

Introduction "Before studying any particular algorithm, we prove the one fact
that every sort ultimately relies on: there is *only one* sorted rearrangement of
a list. Concretely, if `a` and `b` are permutations of each other and both are
sorted in nondecreasing order, then `a = b`. The antisymmetry of `≤` on `ℕ` —
`x ≤ y` and `y ≤ x` force `x = y` — is what pins the ordering down."

/-- **Uniqueness of sorted permutations.** Two sorted lists that are permutations
of each other are equal. -/
Statement sorted_perm_unique {a b : List ℕ} (h : List.Perm a b)
    (ha : a.Pairwise (· ≤ ·)) (hb : b.Pairwise (· ≤ ·)) : a = b := by
  Hint "Mathlib packages exactly this as `List.Perm.eq_of_pairwise`; it asks you
  to supply antisymmetry of the relation. Provide it with `le_antisymm`."
  exact h.eq_of_pairwise (fun _ _ _ _ hxy hyx => le_antisymm hxy hyx) ha hb

Conclusion "This uniqueness result is the backbone of the whole game: it means
every correct sort must produce the very same output."

NewTactic exact
NewTheorem List.Perm.eq_of_pairwise le_antisymm sorted_perm_unique
