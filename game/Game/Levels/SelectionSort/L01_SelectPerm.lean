import Game.Metadata
import Game.Support.SelectionSort

open Game.Clockwork

World "SelectionSort"
Level 1
Title "Selecting the Minimum Rearranges"

Introduction "Selection sort is built from two functions. The first,
`Game.Clockwork.select x s`, scans `s` carrying a running candidate
minimum `x` and returns a pair: the overall minimum, and the remaining elements
in their original order. First prove that this only rearranges elements — the
minimum consed onto the leftovers is a permutation of `x :: s`."

/-- `select` neither loses nor duplicates elements. -/
Statement select_perm (x : ℕ) (s : List ℕ) :
    List.Perm ((select x s).1 :: (select x s).2) (x :: s) := by
  Hint "Induct on `s` (generalizing `x`), unfold `Game.Clockwork.select`,
  and split on the comparison. In each branch chain `List.Perm.swap` and
  `List.Perm.cons` with the induction hypothesis."
  induction s generalizing x with
  | nil => simp [select]
  | cons y ys ih =>
    simp only [select]
    split <;> rename_i h
    · exact ((List.Perm.swap _ _ _).trans (List.Perm.cons y (ih x))).trans (List.Perm.swap _ _ _)
    · exact (List.Perm.swap _ _ _).trans (List.Perm.cons x (ih y))

Conclusion "Selection preserves every element and its multiplicity."

NewDefinition Game.Clockwork.select List
NewTactic induction simp split rename_i exact
NewTheorem List.Perm.cons List.Perm.swap select_perm
