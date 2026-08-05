import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 7
Title "Hash Insert Correctness"

Introduction "Chained insertion adds the key to the front of its own
bucket, so it must be discoverable right away. `Function.update_self`
resolves the updated bucket at exactly the point it was written."

Statement {α : Type} [DecidableEq α] (hash : α → Nat) (x : α) (table : HashTable α) :
    HashTable.lookup hash x (HashTable.insert hash x table) := by
  Hint "Unfold `lookup` and `insert`; `Function.update_self` simplifies the
  updated bucket at `hash x`, which now starts with `x`."
  unfold HashTable.lookup HashTable.insert
  simp [Function.update_self]

Conclusion "Verified: a key inserted into a hash table is immediately found by lookup."

NewDefinition Game.DataStructures.HashTable.insert
NewTheorem Function.update_self
