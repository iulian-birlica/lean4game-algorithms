import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 9
Title "Zero Buckets Have Zero Entries"

Introduction "Even a nonempty hash table contributes nothing when the bucket
budget is `0`, because `entryCount` sums over `List.range 0`, which is empty."

Statement {α : Type} [DecidableEq α] (table : HashTable α) :
    HashLoad.entryCount 0 table = 0 := by
  Hint "Unfold `entryCount`; the map runs over `List.range 0 = []`, so the
  resulting sum is empty."
  simp [HashLoad.entryCount]

Conclusion "Verified: zero buckets always mean zero counted entries."
