import Game.Metadata
import Game.Support.Contracts

World "HoareTriples"
Level 2
Title "GCD Specification"
-- source: RequestProject Lab01.gcd_spec (ported from game W01-L02)

Introduction "Prove the greatest-common-divisor contract: the result divides
both inputs, and any common divisor divides it too."

Statement (a b : Nat) :
    (Game.Contracts.gcd a b ∣ a) ∧ (Game.Contracts.gcd a b ∣ b) ∧
      (∀ d, d ∣ a → d ∣ b → d ∣ Game.Contracts.gcd a b) := by
  Hint "Use the three standard `gcd` cards."
  Hint (hidden := true) "Try `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, and `Nat.dvd_gcd`."
  exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b, fun _ hd_a hd_b => Nat.dvd_gcd hd_a hd_b⟩

Conclusion "Verified: the greatest common divisor contract holds."

NewDefinition Game.Contracts.gcd
NewTheorem Nat.gcd_dvd_left Nat.gcd_dvd_right Nat.dvd_gcd
