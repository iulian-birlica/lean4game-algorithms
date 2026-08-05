import Game.Metadata
import Game.Support.Contracts

World "HoareTriples"
Level 4
Title "Remove First Preserves Permutation"
-- source: RequestProject Lab01.removeFirst_spec (ported from game W01-L04)

Introduction "Removing one occurrence of `x` and putting it back should
reconstruct a permutation of the original list."

Statement {T : Type} [DecidableEq T] (values : List T) (x : T) (hx : x ∈ values) :
    (x :: Game.Contracts.removeFirst values x).Perm values := by
  Hint "The erase-permutation card has the opposite orientation — flip it."
  apply List.Perm.symm
  Hint (hidden := true) "Use `List.perm_cons_erase {hx}`."
  exact List.perm_cons_erase hx

Conclusion "Removed and restored: the permutation holds."

NewTactic apply
NewDefinition Game.Contracts.removeFirst
NewTheorem List.Perm.symm List.perm_cons_erase
