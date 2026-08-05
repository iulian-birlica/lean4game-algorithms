import Game.Metadata
import Game.Levels.ApproximationAlgorithms.L08_HarmonicAccounting
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 9
Title "Greedy Set Cover Is Logarithmic"
-- source: ../game/Game/Worlds/W11Approximation/L09SetCoverLogApprox.lean

Introduction "Turn the harmonic charging formula into the standard
`1 + log n` approximation guarantee for greedy set cover."

Statement {α : Type} (feasible : α → Prop) (cost : α → ℝ)
    (cert : SetCoverCertificate α feasible cost) :
    WithinFactor feasible cost cert.costOptimum
      (1 + Real.log cert.initialUncovered) cert.chosen := by
  Hint "Start from the certificate's charging bound, rewrite it with the
  previous level, then apply `harmonic_le_one_add_log`."
  constructor
  · exact cert.isFeasible
  · have hbound : greedySetCoverBound cert.costOptimum cert.initialUncovered =
        (harmonic cert.initialUncovered : ℝ) * cert.costOptimum := by
      induction' cert.initialUncovered with n ih
      · norm_num [greedySetCoverBound, harmonic]
      · convert congr_arg (· + cert.costOptimum / (n + 1)) ih using 1
        rw [harmonic_succ]
        push_cast
        ring
    have hcharge := cert.chargingBound
    rw [hbound] at hcharge
    calc
      cost cert.chosen ≤ (harmonic cert.initialUncovered : ℝ) * cert.costOptimum :=
        hcharge
      _ ≤ (1 + Real.log cert.initialUncovered) * cert.costOptimum := by
        exact mul_le_mul_of_nonneg_right
          (harmonic_le_one_add_log cert.initialUncovered) cert.optimum_nonneg

Conclusion "The greedy set-cover bound becomes logarithmic."

NewDefinition Game.Approximation.SetCoverCertificate
NewTactic constructor exact «have» rw
NewTheorem harmonic_le_one_add_log mul_le_mul_of_nonneg_right
