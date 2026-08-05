import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 7
Title "Kadane Invariant"
-- source: RequestProject Lab09.kadaneAux_eq, Lab09.kadane_eq

Introduction "Kadane's algorithm is a single left-to-right pass carrying
the accumulator `(best prefix sum, best block sum)`. Prove the loop
invariant: the accumulator computes exactly the reference quantities
`maxPrefixSum`/`maxSubSum`."

Statement (l : List ℤ) :
    kadaneAux l = (maxPrefixSum l, maxSubSum l) ∧ kadane l = maxSubSum l := by
  Hint "Prove the invariant by induction on `l` first, then read off `kadane`
  from its second component."
  have h : kadaneAux l = (maxPrefixSum l, maxSubSum l) := by
    induction' l with x xs ih
    · rfl
    · Hint (hidden := true) "`simp [maxSubSum, maxPrefixSum]`, rewrite `kadaneAux` on the
      cons case, then use the induction hypothesis and `aesop`."
      simp [maxSubSum, maxPrefixSum]
      rw [show kadaneAux (x :: xs) = (max 0 (x + (kadaneAux xs).1),
        max (max 0 (x + (kadaneAux xs).1)) (kadaneAux xs).2) from rfl, ih]
      aesop
  exact ⟨h, congr_arg Prod.snd h⟩

Conclusion "Verified: the one-pass accumulator computes the reference maxima."

NewDefinition Game.Design.kadaneAux Game.Design.kadane Game.Design.maxPrefixSum
  Game.Design.maxSubSum
NewTactic aesop «from»
NewTheorem congr_arg Prod.snd
