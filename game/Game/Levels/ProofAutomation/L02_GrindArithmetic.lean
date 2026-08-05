import Game.Metadata

World "ProofAutomation"
Level 2
Title "Grind Arithmetic"
-- source: RequestProject Lab18.le_trans_grind, Lab18.mod_two_grind, Lab18.counter_bound_grind

Introduction "`grind` is a much heavier engine than `aesop` — closer to an SMT solver: case
splitting, congruence closure, and linear arithmetic together, learning facts as it goes. It
shines on goals mixing arithmetic with case analysis: transitivity of `≤`, parity by cases,
and a bounded-counter fact each need only a line."

Statement :
    (∀ (a b c : ℤ), a ≤ b → b ≤ c → a ≤ c) ∧
    (∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1) ∧
    (∀ (i n : ℕ), i < n → i + 1 ≤ n) := by
  Hint "Each fact is independently closed by `grind` — it performs the case-split/arithmetic
  reasoning a hand proof would need several lemmas (or `omega` plus a manual case split) for."
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind

Conclusion "Verified: `grind` chains inequalities, splits on parity, and closes bounded
counter arithmetic in one step each."

NewTactic grind intros
