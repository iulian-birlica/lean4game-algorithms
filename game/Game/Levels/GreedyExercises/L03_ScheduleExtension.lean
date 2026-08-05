import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 3
Title "Schedule Extension"

Introduction "A schedule is pairwise compatible. To put one activity at the
front, prove it is compatible with every activity already in the schedule, and
reuse the old schedule invariant for the tail."

/-- Prefixing an activity compatible with the whole tail preserves schedule feasibility. -/
Statement (activity : Activity) (schedule : List Activity)
    (hschedule : IsSchedule schedule)
    (hcompat : ∀ next ∈ schedule, Compatible activity next) :
    IsSchedule (activity :: schedule) := by
  Hint "Unfold `IsSchedule`; `List.Pairwise.cons` asks for compatibility with
  every tail element and the old pairwise proof."
  unfold IsSchedule at hschedule ⊢
  exact List.Pairwise.cons hcompat hschedule

Conclusion "The schedule can be extended at the front once the new activity fits every old one."

NewTactic exact unfold
NewDefinition Game.Greedy.IsSchedule
NewTheorem List.Pairwise.cons
