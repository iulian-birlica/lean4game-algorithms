import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "AmortizedAnalysis"
Level 4
Title "Potential Method for Sequences"
-- source: RequestProject Lab17.potential_method_seq (demo), Lab17.potential_method_seq_le

Introduction "Real data structures support *several* operations, chosen
by the caller — a *list* of operations `ops : List Op`, not a single
repeated one. `potential_method_seq` (given) upgrades the potential
method to this setting, with a data-structure invariant `Inv` the
operations must preserve. Derive the usable form, exactly as before but
now for a whole operation list."

Statement {S Op : Type*} (step : Op → S → S) (cost : Op → S → ℕ) (Phi : S → ℕ) (c : ℕ)
    (Inv : S → Prop) (hpres : ∀ op s, Inv s → Inv (step op s))
    (h : ∀ op s, Inv s → cost op s + Phi (step op s) ≤ c + Phi s)
    (ops : List Op) (s : S) (hs : Inv s) :
    totalCostL step cost ops s ≤ c * ops.length + Phi s := by
  Hint "Instantiate the given telescoped bound `potential_method_seq`, then drop the
  non-negative potential term via `Nat.le_add_right`."
  convert potential_method_seq step cost Phi c Inv hpres h ops s hs |> le_trans _
  exact Nat.le_add_right _ _

Conclusion "Verified: the potential method's telescoped bound gives the usable total-cost form,
for a whole operation list."

NewDefinition Game.Clockwork.totalCostL Game.Clockwork.stateAfterL
NewTheorem Game.Clockwork.potential_method_seq Nat.le_add_right
