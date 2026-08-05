import Game.Metadata
import Game.Support.RadixSort

open Game.Clockwork

World "RadixSort"
Level 1
Title "One Pass Rearranges"

Introduction "Radix sort is a *non-comparison* sort: it never compares two
elements, it only inspects individual bits. Its building block is
`Game.Clockwork.bitPass i s`, which keeps the elements whose bit `i` is
`0` (in order) followed by those whose bit `i` is `1` (in order). First prove
this only rearranges the list."

/-- A single bit pass is a permutation of its input. -/
Statement bitPass_perm (i : ℕ) (s : List ℕ) : List.Perm (bitPass i s) s := by
  Hint "Unfold `Game.Clockwork.bitPass`; the two filters partition `s`,
  so `List.filter_append_perm` applies directly."
  unfold bitPass
  exact List.filter_append_perm (fun x => x / 2 ^ i % 2 == 0) s

Conclusion "A single pass preserves every element and its multiplicity."

NewDefinition Game.Clockwork.bitPass List
NewTactic unfold exact
NewTheorem List.filter_append_perm bitPass_perm
