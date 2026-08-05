import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "AmortizedAnalysis"
Level 3
Title "Binary Counter Amortized Bound"
-- source: RequestProject Lab16.binaryCounter_potential

Introduction "Assemble the pieces: starting from the all-zero counter
(zero potential), any sequence of `n` increments costs at most `2n`
bit-writes in total — `Increment` runs in `O(1)` amortized time, even
though a single increment can cost the full width of the counter."

Statement (n : ℕ) : totalCost increment incCost n [] ≤ 2 * n := by
  Hint "Instantiate `potential_method_le` at the counter's own amortized bound
  `increment_amortized`, starting from `[]`; the starting potential is `0`."
  have := potential_method_le increment incCost Phi 2 increment_amortized n []
  simpa only [ge_iff_le, Phi_nil, add_zero] using this

Conclusion "Verified: the binary counter's increment is amortized O(1)."

NewTheorem Game.Clockwork.potential_method_le Game.Clockwork.increment_amortized
  ge_iff_le
