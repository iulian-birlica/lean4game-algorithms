import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L09_BigOmegaDefinition

open Game.Clockwork

World "Asymptotics"
Level 10
Title "Small-o Is Stronger"

Introduction "`f =o g` is stronger than `f =O g`: instead of one fixed
constant bound, it works for every positive `ε`. To recover Big-O, just pick
`ε = 1`."

/-- Every little-o bound is automatically a Big-O bound. -/
Statement smallo_imp_bigO (f g : ℕ → ℝ) : f =o g → f =O g := by
  Hint "Assume `f =o g`, then specialize the definition to `ε = 1`."
  intro h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  use 1
  · norm_num
  use N
  Hint (hidden := true) "The witness you got from `ε = 1` already has exactly the inequality you need."
  intro n hn
  simpa using hN n hn

Conclusion "Little-o says a function is eventually smaller than every
positive multiple of `g`, so in particular it is smaller than `1 · g`."

NewDefinition Game.Clockwork.IsLittleO
NewTheorem smallo_imp_bigO
