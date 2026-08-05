import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 2
Title "Activity Exchange"

Introduction "The exchange argument replaces the first scheduled activity by one
that finishes no later. If `first` can be followed by `next`, then the earlier
finishing `candidate` can also be followed by `next`."

/-- Replacing an activity by one that finishes earlier preserves compatibility with the next activity. -/
Statement (candidate first next : Activity)
    (hfinish : candidate.finish ≤ first.finish)
    (hcompat : Compatible first next) :
    Compatible candidate next := by
  Hint "`Compatible first next` is the inequality `first.finish ≤ next.start`.
  Chain it after the earlier-finish hypothesis."
  exact le_trans hfinish hcompat

Conclusion "The first exchange step preserves non-overlap with the following activity."

NewTactic exact
NewDefinition Game.Greedy.Compatible Game.Greedy.Activity.start
NewTheorem le_trans
