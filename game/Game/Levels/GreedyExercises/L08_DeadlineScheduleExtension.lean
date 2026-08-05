import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 8
Title "Deadline Schedule Extension"

Introduction "A feasible deadline schedule can be extended at the end when the
new job still finishes by its deadline after all existing work. Prove the
general version with an arbitrary elapsed time, then specialize to zero."

/-- Appending one on-time job to a feasible schedule preserves deadline feasibility. -/
Statement (jobs : List Job) (job : Job)
    (hjobs : MeetsDeadlines 0 jobs)
    (hdeadline : scheduledTime jobs + job.duration ≤ job.deadline) :
    MeetsDeadlines 0 (jobs ++ [job]) := by
  Hint "Induct through `jobs`, keeping `elapsed` general. The recursive call
  shifts elapsed time by the current job's duration."
  have append_deadline :
      ∀ (elapsed : Nat) (jobs : List Job),
        MeetsDeadlines elapsed jobs →
        elapsed + scheduledTime jobs + job.duration ≤ job.deadline →
        MeetsDeadlines elapsed (jobs ++ [job]) := by
    intro elapsed jobs
    induction jobs generalizing elapsed with
    | nil =>
        intro _ h
        simp [MeetsDeadlines, scheduledTime] at h ⊢
        exact h
    | cons current rest ih =>
        intro hfeasible h
        simp [MeetsDeadlines] at hfeasible ⊢
        constructor
        · exact hfeasible.1
        · apply ih
          · exact hfeasible.2
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  exact append_deadline 0 jobs hjobs (by simpa [Nat.zero_add] using hdeadline)

Conclusion "The deadline schedule remains feasible after appending the new on-time job."

NewTactic apply constructor exact «have» induction intro simpa simp
NewDefinition Game.Greedy.Job Game.Greedy.Job.duration Game.Greedy.Job.deadline
  Game.Greedy.MeetsDeadlines Game.Greedy.scheduledTime
NewTheorem Nat.add_assoc Nat.add_comm Nat.add_left_comm Nat.zero_add
