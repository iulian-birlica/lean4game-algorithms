import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 11
Title "Set Sum Distributes"
-- source: RequestProject Lab02.sum_add_distrib_set

Introduction "Now use induction on sets. Every set is built one element at a
time: it is either empty, or `insert a s` for some smaller `s` with `a ∉ s`.
Prove that sums distribute over pointwise addition."

Statement {α : Type} [DecidableEq α] (s : Finset α) (f g : α → ℕ) :
    (∑ x ∈ s, (f x + g x)) = (∑ x ∈ s, f x) + (∑ x ∈ s, g x) := by
  Hint "`induction s using Finset.induction_on with` gives an `empty` case and an
  `insert` case; the step peels off one element with the `sum_insert` card."
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, Nat.add_zero]
  | @insert a s h ih =>
    Hint (hidden := true) "`rw [sum_insert h]` three times, then the induction
    hypothesis, then `ring`."
    rw [Finset.sum_insert h, Finset.sum_insert h, Finset.sum_insert h, ih]
    ring

Conclusion "Assembled: sums over a set distribute over addition."

NewTheorem Finset.induction_on Finset.sum_empty Nat.add_zero
