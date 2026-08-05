import Game.Metadata
import Game.Support.Contracts

World "HoareTripleExercises"
Level 6
Title "Subtractive GCD"
-- source: RequestProject Lab04.gcdSub_spec

Introduction "Euclid's subtractive algorithm: repeatedly replace the larger
argument by the difference. Its loop invariant is that `gcd` is unchanged
by each subtraction step — prove `gcdSub` computes `Nat.gcd`."

Statement (a b : ℕ) : Game.Contracts.gcdSub a b = Nat.gcd a b := by
  Hint "Induct with `gcdSub.induct` — five cases, one per branch of the `if`
  chain in the definition."
  induction a, b using Game.Contracts.gcdSub.induct with
  | case1 b => rw [Game.Contracts.gcdSub, if_pos rfl, Nat.gcd_zero_left]
  | case2 a ha => rw [Game.Contracts.gcdSub, if_neg ha, if_pos rfl, Nat.gcd_zero_right]
  | case3 b h1 h2 => rw [Game.Contracts.gcdSub, if_neg h1, if_neg h2, if_pos rfl, Nat.gcd_self]
  | case4 a b ha hb hab hlt ih =>
    Hint (hidden := true) "`b < a`: replace `a` by `a - b`; `gcd` is invariant under this
    subtraction (`Nat.gcd_sub_self_left`)."
    rw [Game.Contracts.gcdSub, if_neg ha, if_neg hb, if_neg hab, if_pos hlt, ih,
      Nat.gcd_sub_self_left (le_of_lt hlt)]
  | case5 a b ha hb hab hlt ih =>
    Hint (hidden := true) "`a ≤ b`: replace `b` by `b - a`, symmetrically."
    rw [Game.Contracts.gcdSub, if_neg ha, if_neg hb, if_neg hab, if_neg hlt, ih,
      Nat.gcd_sub_self_right (not_lt.mp hlt)]

Conclusion "Verified: subtractive gcd agrees with `Nat.gcd`, always."

NewDefinition Game.Contracts.gcdSub Game.Contracts.gcdSub.induct
NewTheorem Nat.gcd_zero_left Nat.gcd_zero_right Nat.gcd_self Nat.gcd_sub_self_left
  Nat.gcd_sub_self_right not_lt
