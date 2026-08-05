import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 1
Title "Earliest-Finish Choice"

Introduction "Activity selection starts by choosing an activity that finishes as
early as possible. If `candidate` is earliest among `first :: rest`, it
certainly finishes no later than the visible head `first`."

/-- An earliest-finishing activity beats the first available activity's finish time. -/
Statement (candidate first : Activity) (rest : List Activity)
    (h : EarliestFinish candidate (first :: rest)) :
    candidate.finish ≤ first.finish := by
  Hint "Apply the earliest-finish hypothesis to `first`; membership in
  `first :: rest` is immediate by simplification."
  exact h first (by simp)

Conclusion "The earliest-finish choice is bounded by the head of the activity list."

NewTactic exact simp
NewDefinition Game.Greedy.Activity Game.Greedy.Activity.finish Game.Greedy.EarliestFinish
