import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork
open Cslib.Algorithms.Lean

World "TimedComputation"
Level 2
Title "Time Cost Function"
-- source: RequestProject Lab11.timeCost_tick, Lab11.isBigO_of_timeCost_le

Introduction "The bridge from the `TimeM` cost monad to the Landau
vocabulary above: a routine that just ticks `g n` has cost function
exactly `g`, and a pointwise time bound between two routines yields a
big-O relationship between their cost functions."

Statement {α β : Type*} (g : ℕ → ℝ) (run₁ : ℕ → TimeM ℝ α) (run₂ : ℕ → TimeM ℝ β)
    (hnn₁ : ∀ n, 0 ≤ (run₁ n).time) (hnn₂ : ∀ n, 0 ≤ (run₂ n).time)
    {C : ℝ} (hC : 0 < C) {N : ℕ} (hle : ∀ n ≥ N, (run₁ n).time ≤ C * (run₂ n).time) :
    timeCost (fun n => TimeM.tick (g n)) = g ∧ timeCost run₁ =O timeCost run₂ := by
  Hint "The first fact is definitional; the second assembles directly from
  the pointwise time bound."
  constructor
  · rfl
  · Hint (hidden := true) "`use C, hC, N`, then unfold `timeCost` via `timeCost_apply` and
    apply `hle`."
    use C, hC, N
    exact fun n hn => by
      simpa only [abs_of_nonneg (hnn₁ n), abs_of_nonneg (hnn₂ n), timeCost_apply] using hle n hn

Conclusion "Time-cost bridge complete: pointwise time bounds transfer to big-O cost bounds."

NewDefinition Game.Clockwork.timeCost Cslib.Algorithms.Lean.TimeM
  Cslib.Algorithms.Lean.TimeM.tick
NewTheorem Game.Clockwork.timeCost_apply
