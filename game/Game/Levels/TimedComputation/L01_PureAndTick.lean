import Game.Metadata
import Game.Support.TimeM

open Cslib.Algorithms.Lean

World "TimedComputation"
Level 1
Title "Pure Values and Ticks"

Introduction "A `TimeM` computation records two pieces of data: the value it
returns and the time it spent. Pure computations return their input at zero
cost, while `TimeM.tick` spends the requested cost and returns no interesting
value."

Statement {α : Type*} (a : α) (c : ℕ) :
    (pure a : TimeM ℕ α).ret = a ∧
    (pure a : TimeM ℕ α).time = 0 ∧
    (TimeM.tick c).ret = () ∧
    (TimeM.tick c).time = c := by
  Hint "Each field equation follows from the definition of `pure` or
  `TimeM.tick`. The named simp facts are also available."
  constructor
  · exact TimeM.ret_pure a
  · constructor
    · exact TimeM.time_pure a
    · constructor
      · exact TimeM.ret_tick c
      · exact TimeM.time_tick c

Conclusion "You can now read a timed computation by separating its returned
value from its accumulated cost."

NewDefinition Cslib.Algorithms.Lean.TimeM Cslib.Algorithms.Lean.TimeM.ret
  Cslib.Algorithms.Lean.TimeM.time Cslib.Algorithms.Lean.TimeM.tick

NewTheorem Cslib.Algorithms.Lean.TimeM.ret_pure
  Cslib.Algorithms.Lean.TimeM.time_pure
  Cslib.Algorithms.Lean.TimeM.ret_tick
  Cslib.Algorithms.Lean.TimeM.time_tick
