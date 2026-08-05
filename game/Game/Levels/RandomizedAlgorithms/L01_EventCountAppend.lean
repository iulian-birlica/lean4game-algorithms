import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 1
Title "Count Successful Seeds"
-- source: ../game/Game/Worlds/W10Randomized/L01EventCounting.lean

Introduction "If a random experiment is split into two batches of seeds, the
number of successful seeds should split the same way."

Statement (σ : Type) (left right : List σ) (event : σ → Bool) :
    eventCount (left ++ right) event = eventCount left event + eventCount right event := by
  Hint "Unfold `eventCount` and let the list lemmas for `filter` and `length`
  handle append."
  simp [eventCount, List.filter_append]

Conclusion "Successful-seed counting now respects list append."

NewDefinition Game.Randomized.eventCount
NewTheorem List.filter_append
