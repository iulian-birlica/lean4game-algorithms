import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 1
Title "Carried Knapsack Value"

Introduction "`knapCarry` is the dynamic-programming version of a
proof-carrying value. It returns `{ v : ℕ // knap items c = v }`: a number
bundled with a proof that this number is the reference DP value.

The executable `knapImpl` is just the carried number. Correctness is the
proof already stored beside it."

Statement (items : List KItem) (c : ℕ) :
    knapImpl items c = knap items c := by
  Hint "`knapImpl` is the value part of `knapCarry`; the proof component has
  the equality in the opposite direction."
  Hint (hidden := true) "`exact (knapCarry items c).2.symm`."
  exact (knapCarry items c).2.symm

Conclusion "The certified DP implementation matches the reference recurrence
because the implementation carries that proof with its value."

NewDefinition Game.Design.KItem Game.Design.KItem.w Game.Design.KItem.v Game.Design.knap Game.Design.knapCarry Game.Design.knapImpl
