import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 5
Title "Euclid's Termination Bound"
-- source: ../game/Game/Worlds/W12Numeric/L05EuclidStepBound.lean

Introduction "Each nonterminal Euclid step replaces the second argument by a
strictly smaller remainder. Use that to show the number of remainder calls is
at most the starting second argument."

Statement (a b : Nat) :
    euclidSteps a b ≤ b := by
  Hint "Use strong induction on `b`; after unfolding `euclidSteps`, the
  recursive case reduces to the strict inequality `a % b < b`."
  induction' b using Nat.strong_induction_on with b ih generalizing a
  unfold euclidSteps
  split_ifs <;> simp +arith +decide [*]
  exact lt_of_le_of_lt
    (ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)) _)
    (Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›))

Conclusion "Euclid's algorithm makes only finitely many remainder calls."

NewDefinition Game.Numeric.euclidSteps
NewTactic induction' unfold split_ifs simp exact
NewTheorem Nat.mod_lt Nat.pos_of_ne_zero lt_of_le_of_lt
