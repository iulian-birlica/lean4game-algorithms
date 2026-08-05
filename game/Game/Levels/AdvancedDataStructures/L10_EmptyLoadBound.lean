import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 10
Title "Empty Table Load Bound"

Introduction "A load-factor bound compares total stored entries against the
number of buckets. Since the empty table has zero counted entries, it should
satisfy every such bound automatically."

Statement {α : Type} [DecidableEq α]
    (bucketCount numerator denominator : Nat) :
    HashLoad.LoadAtMost bucketCount numerator denominator
      (HashTable.empty : HashTable α) := by
  Hint "Unfold `LoadAtMost`, then rewrite the empty table's entry count to
  `0` and simplify the arithmetic."
  simp [HashLoad.LoadAtMost, HashLoad.entryCount, HashTable.empty]

Conclusion "Verified: the empty table satisfies every basic load bound."

NewDefinition Game.DataStructures.HashLoad.LoadAtMost
