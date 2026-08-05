import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 6
Title "Empty Hash Lookup"

Introduction "A chained hash table stores its entries in per-hash buckets.
Switch domains from search trees to hashing: the empty table's every
bucket is empty, so no key can occur in it."

Statement {α : Type} [DecidableEq α] (hash : α → Nat) (x : α) :
    ¬ HashTable.lookup hash x HashTable.empty := by
  Hint "Unfold `lookup` and `empty`: the bucket at `hash x` is `[]`, which
  contains nothing."
  simp [HashTable.lookup, HashTable.empty]

Conclusion "Verified: the empty hash table answers every lookup with failure."

NewDefinition Game.DataStructures.HashTable Game.DataStructures.HashTable.empty
  Game.DataStructures.HashTable.lookup
