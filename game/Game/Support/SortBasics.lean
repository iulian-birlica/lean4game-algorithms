import Mathlib

namespace Game.Clockwork

/-- A function `f : List ℕ → List ℕ` *is a sorting function* when, for every
input list, its output is a permutation of that input and is sorted in
nondecreasing order.

This is the single common contract that every sort in this game satisfies: the
comparison sorts (insertion, selection) satisfy it unconditionally, and the
non-comparison sort (radix) satisfies it once its inputs fit in the given number
of bits. Bundling the two halves of correctness into one predicate lets us state
the shared facts — above all, that any two sorting functions agree — once and for
all. -/
def IsSort (f : List ℕ → List ℕ) : Prop :=
  ∀ s : List ℕ, List.Perm (f s) s ∧ (f s).Pairwise (· ≤ ·)

end Game.Clockwork
