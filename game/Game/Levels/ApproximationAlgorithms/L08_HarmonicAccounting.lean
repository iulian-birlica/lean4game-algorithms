import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 8
Title "Harmonic Set-Cover Accounting"
-- source: ../game/Game/Worlds/W11Approximation/L08HarmonicAccounting.lean

Introduction "Solve the set-cover charging recurrence as harmonic growth:
`greedySetCoverBound optimum n = H_n * optimum`."

Statement (optimum : ℝ) (n : Nat) :
    greedySetCoverBound optimum n = (harmonic n : ℝ) * optimum := by
  Hint "Induct on `n`. In the successor step, unfold the recurrence and use
  `harmonic_succ` before rearranging with `ring`."
  induction' n with n ih
  · norm_num [greedySetCoverBound, harmonic]
  · convert congr_arg (· + optimum / (n + 1)) ih using 1
    rw [harmonic_succ]
    push_cast
    ring

Conclusion "The greedy charging bound is now expressed with harmonic numbers."

NewTactic intro induction' norm_num rw push_cast ring
NewTheorem harmonic_succ
