import Game.Metadata
import Game.Support.LowerBounds

open Game.Complexity
open Game.LowerBounds

World "LowerBounds"
Level 9
Title "Transport a Conditional Lower Bound"
-- source: ../game/Game/Worlds/W14LowerBounds/L09TransportedCollapse.lean

Introduction "If an NP-complete source reduces to a fast target, pull the fast
algorithm back along the reduction and then apply the NP-hard collapse
argument."

Statement (source target : DecisionProblem) :
    NPComplete source → Reduces source target → inP target → P = NP := by
  Hint "First transport `inP` back to `source`, then use the hardness half of
  `NPComplete source`."
  intro hsource hred htarget
  exact p_eq_np_of_hard_in_p hsource.2 (inP_of_reduces hred htarget)

Conclusion "Conditional lower bounds move across polynomial reductions."
