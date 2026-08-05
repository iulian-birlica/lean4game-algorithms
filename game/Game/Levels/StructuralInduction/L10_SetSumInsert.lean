import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 10
Title "Set Sum Insert"
-- source: RequestProject Lab02.sum_add_distrib_set

Introduction "Lean's type name here is `Finset`, but you can read it as a
finite set, or just a set. The basic sum step says that if `a` is not already
in the set, then summing over `insert a s` peels off `f a` and leaves the sum
over `s`."

Statement {α : Type} [DecidableEq α] (a : α) (s : Finset α) (f : α → ℕ)
    (h : a ∉ s) :
    (∑ x ∈ insert a s, f x) = f a + (∑ x ∈ s, f x) := by
  Hint "Use the theorem that rewrites a sum over `insert a s` when you know `a ∉ s`."
  rw [Finset.sum_insert h]

Conclusion "Unpacked: summing over an inserted element is one value plus the old sum."

NewDefinition Insert.insert
NewTheorem Finset.sum_insert
