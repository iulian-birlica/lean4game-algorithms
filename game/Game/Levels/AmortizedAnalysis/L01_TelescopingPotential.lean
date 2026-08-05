import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "AmortizedAnalysis"
Level 1
Title "Telescoping Potential"
-- source: RequestProject Lab16.potential_method (demo), Lab16.potential_method_le

Introduction "**Amortized analysis.** Some operations are cheap most of
the time but occasionally expensive; judging by worst case alone is
misleading. The **potential method** attaches a number `Phi state ≥ 0`
to the structure and lets expensive operations be paid for by a drop in
potential. `potential_method` (given) shows that if every operation's
*amortized* cost — actual cost plus the change in potential — is at most
a constant `c`, then the costs telescope along any sequence of `n`
operations. Derive the usable form: because `Phi` is non-negative, the
total actual cost is at most `c * n` plus the starting potential."

Statement {S : Type*} (next : S → S) (cost Phi : S → ℕ) (c : ℕ)
    (h : ∀ s, cost s + Phi (next s) ≤ c + Phi s) (n : ℕ) (s : S) :
    totalCost next cost n s ≤ c * n + Phi s := by
  Hint "Instantiate the given telescoped bound `potential_method`, then drop the (non-negative)
  potential term on the left with `omega`."
  have := potential_method next cost Phi c h n s
  omega

Conclusion "Verified: the potential method's telescoped bound gives the usable total-cost form."

NewDefinition Game.Clockwork.totalCost Game.Clockwork.stateAfter
NewTheorem Game.Clockwork.potential_method
