import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 6
Title "Busy Beaver Bound"
-- source: RequestProject Lab22.haltTime_le_bbSteps

Introduction "`bbSteps n` is the maximum halting time among all programs whose code number is
at most `n` — a finite supremum, hence well-defined for every `n`, even though (as the next
level shows) it is not computable. Prove `bbSteps` really is an upper bound: every program's
halting time is recorded at its own code number."

Statement (c : Nat.Partrec.Code) : haltTime c ≤ bbSteps (Encodable.encode c) := by
  Hint "`bbSteps` is a `Finset.sup` over code numbers `≤ n`; `c`'s own code number is in that
  range, and the summand there decodes back to `c` (`Encodable.encodek`)."
  have hmem : Encodable.encode c ∈ Finset.range (Encodable.encode c + 1) := by simp
  refine le_trans ?_ (Finset.le_sup (f := (fun m =>
    match (Encodable.decode m : Option Nat.Partrec.Code) with
    | some c => haltTime c
    | Option.none => 0)) hmem)
  simp only [Encodable.encodek, le_refl]

Conclusion "Verified: `bbSteps` bounds every program's halting time at its own code number."

NewDefinition Game.Complexity.bbSteps Option.none Option.some Encodable.encode Encodable.decode
NewTheorem Finset.le_sup Encodable.encodek
