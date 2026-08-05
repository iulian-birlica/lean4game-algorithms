import Game.Metadata
import Game.Support.Contracts

World "HoareTripleExercises"
Level 5
Title "Digit Count Correctness"
-- source: RequestProject Lab04.countDigits_spec

Introduction "`countDigits` strips one decimal digit per loop step. Prove
it computes the same count as `Nat.digits 10 n`'s length — induction on
the recursion, mirroring the code line for line."

Statement (n : ℕ) : Game.Contracts.countDigits n = (Nat.digits 10 n).length := by
  Hint "Induct with `countDigits.induct`; the positive case peels off one digit
  via `Nat.digits_def'`."
  induction n using Game.Contracts.countDigits.induct with
  | case1 x hx ih =>
    Hint (hidden := true) "`rw [countDigits, if_pos hx, Nat.digits_def' (by norm_num) hx,
    List.length_cons, ih]`."
    rw [Game.Contracts.countDigits, if_pos hx, Nat.digits_def' (by norm_num : 1 < 10) hx,
      List.length_cons, ih]
  | case2 x hx =>
    have hx0 : x = 0 := by omega
    rw [Game.Contracts.countDigits, if_neg hx, hx0, Nat.digits_zero, List.length_nil]

Conclusion "Verified: `countDigits` counts exactly the base-10 digits of `n`."

NewDefinition Game.Contracts.countDigits Game.Contracts.countDigits.induct
NewTheorem Nat.digits_def' Nat.digits_zero
