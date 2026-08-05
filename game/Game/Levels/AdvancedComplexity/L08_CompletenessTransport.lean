import Game.Metadata
import Game.Support.AdvancedComplexity

open Game.Complexity

World "AdvancedComplexity"
Level 8
Title "Chained NP-Completeness"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L08CompletenessTransport.lean

Introduction "NP-completeness is stable under a chain of reductions: start
from an NP-complete source, keep `target` inside `NP`, and compose the
reduction path."

Statement chained_np_complete (source middle target : DecisionProblem) :
    NPComplete source →
    inNP target →
    Reduces source middle →
    Reduces middle target →
    NPComplete target := by
  Hint "Keep the `inNP target` half, and compose the hardness witness for
  each NP source problem through both reductions."
  intro hsource htarget hsourceMiddle hmiddleTarget
  refine ⟨htarget, ?_⟩
  intro problem hproblem
  exact PolyReducible.trans (hsource.2 problem hproblem)
    (PolyReducible.trans hsourceMiddle hmiddleTarget)

Conclusion "NP-hardness now travels cleanly through reduction pipelines."
