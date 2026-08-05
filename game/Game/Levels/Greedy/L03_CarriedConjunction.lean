import Game.Metadata
import Game.Levels.Greedy.L02_CarriedRewrite

World "Greedy"
Level 3
Title "Carried Conjunction"

Introduction "A certificate can also carry several facts at once. If the proof
component has type `p ∧ q`, then its left half is `.1` and its right half is
`.2`.

The next Greedy certificates use this same pattern: one field identifies the
carried greedy assignment, and another field proves it is feasible."

Statement (n : ℕ)
    (cert : { m : ℕ // m = n ∧ m ≤ n }) :
    cert.1 ≤ n := by
  Hint "`cert.2` is the whole conjunction. Project its right half."
  Hint (hidden := true) "`exact cert.2.2`."
  exact cert.2.2

Conclusion "Nested projections like `.2.2` are just reading a specific proof
out of a bundled certificate."
