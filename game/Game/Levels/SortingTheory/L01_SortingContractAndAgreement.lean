import Game.Metadata
import Game.Support.SortBasics
import Game.Levels.ComparisonSorts.L01_SortedPermUnique

open Game.Clockwork

World "SortingTheory"
Level 1
Title "Sorting Contract and Agreement"

Introduction "We package the two halves of correctness into one predicate,
`IsSort f`, which says that for every input `s` the output
`f s` is a permutation of `s` and is sorted. The preceding comparison-sort
branches prove exactly the two facts needed to satisfy `IsSort`; radix sort
reaches the same sorted-permutation shape under its bit-bound hypothesis.

Now cash in the previous level: if `f` and `g` are *both* sorting functions, they
compute the same result on every input. In other words, there is essentially only
one sorting function — the algorithms differ only in *how* they get there, never
in *what* they return."

/-- **Any two sorting functions agree.** If `f` and `g` both satisfy `IsSort`,
then `f s = g s` for every input `s`. -/
Statement isSort_eq {f g : List ℕ → List ℕ} (hf : IsSort f) (hg : IsSort g) :
    ∀ s, f s = g s := by
  Hint "Fix `s`, then unpack the two contracts with `obtain` to get the four
  facts (`f s ~ s`, `f s` sorted, `g s ~ s`, `g s` sorted)."
  intro s
  obtain ⟨hfp, hfs⟩ := hf s
  obtain ⟨hgp, hgs⟩ := hg s
  Hint "`f s` and `g s` are both permutations of `s`, hence of each other: chain
  `hfp` with the symmetric version of `hgp` using `List.Perm.trans` and
  `List.Perm.symm`. Then finish with `sorted_perm_unique`."
  exact sorted_perm_unique (hfp.trans hgp.symm) hfs hgs

Conclusion "Correctness collapses every unconditional sorting function onto a
single result. The next levels register the concrete comparison sorts against
this shared contract."

NewDefinition Game.Clockwork.IsSort
NewTactic intro obtain exact
NewTheorem List.Perm.trans List.Perm.symm sorted_perm_unique isSort_eq
