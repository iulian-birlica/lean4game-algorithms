import Game.Support.AdvancedComplexity

namespace Game.LowerBounds

open Game.Complexity
open Game.AdvancedComplexity

/-- The equality-search adversary still survives at `target` after the
locations in `queried` have all answered negatively. -/
def AdversarySurvives {α : Type} (queried : Finset α) (target : α) : Prop :=
  target ∉ queried

/-- Transcripts for a binary decision tree of fixed depth. -/
abbrev BinaryTranscript (queries : Nat) := Fin queries → Bool

/-- Transcripts for a decision tree whose each query has `outcomes` many
possible answers. -/
abbrev Transcript (outcomes queries : Nat) := Fin queries → Fin outcomes

/-- An encoding separates hidden instances when it is injective. -/
def Separates {α β : Type} (encode : α → β) : Prop := Function.Injective encode

/-- If an NP-hard target were in `P`, then every NP problem would be in `P`. -/
theorem np_subset_p_of_hard_in_p {target : DecisionProblem}
    (hard : NPHard target) (fast : inP target) : NP ⊆ P := by
  intro source hsource
  exact inP_of_reduces (hard source hsource) fast

/-- A polynomial-time algorithm for an NP-hard problem collapses `P` and
`NP`. -/
theorem p_eq_np_of_hard_in_p {target : DecisionProblem}
    (hard : NPHard target) (fast : inP target) : P = NP := by
  apply Set.Subset.antisymm P_subset_NP
  exact np_subset_p_of_hard_in_p hard fast

end Game.LowerBounds
