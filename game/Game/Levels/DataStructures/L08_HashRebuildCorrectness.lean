import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 8
Title "Hash Rebuild Correctness"

Introduction "Rebuilding folds `insert` over a key list, one key at a time.
Combine `rebuild_cons` with the general insert/lookup characterization
`lookup_insert_iff`, and the recursive case collapses into the same
membership fact `List.mem_cons` already gave for search trees."

Statement {α : Type} [DecidableEq α] (hash : α → Nat) (x : α) (keys : List α) :
    HashTable.lookup hash x (HashTable.rebuild hash keys) ↔ x ∈ keys := by
  Hint "Induct on `keys`. The empty case unfolds directly. In the `cons`
  case, rewrite by `rebuild_cons`, then `lookup_insert_iff`, then the
  induction hypothesis, then `List.mem_cons` to match the goal exactly."
  induction keys with
  | nil => simp [HashTable.rebuild, HashTable.lookup, HashTable.empty]
  | cons a keys ih =>
      rw [HashTable.rebuild_cons, HashTable.lookup_insert_iff, ih, List.mem_cons]

Conclusion "Verified: rebuilding a hash table from a key list preserves exactly that key list's membership."

NewTactic rw
NewDefinition Game.DataStructures.HashTable.rebuild
NewTheorem Game.DataStructures.HashTable.rebuild_cons Game.DataStructures.HashTable.lookup_insert_iff
