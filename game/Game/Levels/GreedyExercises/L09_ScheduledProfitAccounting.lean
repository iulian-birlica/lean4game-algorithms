import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 9
Title "Scheduled Profit Accounting"

Introduction "Deadline scheduling optimizes profit, so the table needs a simple
accounting fact: appending one job adds exactly that job's profit to the total."

/-- Appending one job adds its profit to the schedule's total profit. -/
Statement (jobs : List Job) (job : Job) :
    totalProfit (jobs ++ [job]) = totalProfit jobs + job.profit := by
  Hint "Unfold `totalProfit`; mapping over append and summing a singleton are
  simplification facts."
  unfold totalProfit
  simp [List.map_append, List.sum_append]

Conclusion "Profit accounting is ready for deadline-scheduling exchange arguments."

NewTactic simp unfold
NewDefinition Game.Greedy.totalProfit Game.Greedy.Job.profit
NewTheorem List.map_append List.sum_append
