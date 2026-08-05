import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 8
Title "Empty Table Has Zero Entries"

Introduction "The empty hash table stores no keys in any bucket, so summing
the lengths of its first `bucketCount` buckets should always produce `0`."

Statement {α : Type} [DecidableEq α] (bucketCount : Nat) :
    HashLoad.entryCount bucketCount (HashTable.empty : HashTable α) = 0 := by
  Hint "Unfold `entryCount` and `HashTable.empty`: every bucket lookup returns
  `[]`, whose length is `0`."
  simp [HashLoad.entryCount, HashTable.empty]

Conclusion "Verified: the empty table contributes zero entries."

NewDefinition Game.DataStructures.HashLoad.entryCount
