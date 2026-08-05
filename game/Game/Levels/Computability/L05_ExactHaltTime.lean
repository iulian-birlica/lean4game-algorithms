import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 5
Title "Exact Halt Time"
-- source: RequestProject Lab22.haltTime_spec, Lab22.evaln_isSome_mono

Introduction "One step from decidability to an *uncomputable function*: the **Busy Beaver**.
First, the exact **halting time** of a single program: `haltTime c` is the least step-budget
after which the bounded evaluator `evaln` already reports an answer. Prove `haltTime` is
correct, and that the bounded evaluator is monotone — once a program has halted within `k`
steps, it stays halted for any larger budget."

Statement :
    (∀ {c : Nat.Partrec.Code}, (c.eval 0).Dom →
      (Nat.Partrec.Code.evaln (haltTime c) c 0).isSome) ∧
    (∀ {c : Nat.Partrec.Code} {k N : ℕ}, (Nat.Partrec.Code.evaln k c 0).isSome → k ≤ N →
      (Nat.Partrec.Code.evaln N c 0).isSome) := by
  Hint "Correctness: extract a witnessing step count from `c.eval 0`'s domain proof (via
  `evaln_complete`), then `haltTime` is by definition the least such. Monotonicity: `evaln`
  agrees with the untimed `eval` once it succeeds, so re-running with a larger budget succeeds
  too."
  refine ⟨?_, ?_⟩
  · intro c h
    have hex : ∃ k, (Nat.Partrec.Code.evaln k c 0).isSome := by
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
      rw [Nat.Partrec.Code.evaln_complete] at hx
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by rw [hk]; rfl⟩
    rw [haltTime, dif_pos hex]
    exact Nat.find_spec hex
  · intro c k N hk hN
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
    have : x ∈ Nat.Partrec.Code.evaln N c 0 := Nat.Partrec.Code.evaln_mono hN (by rw [hx]; rfl)
    rw [Option.mem_def] at this
    rw [this]; rfl

Conclusion "Verified: `haltTime` is correct, and once a program halts within a budget it halts
within any larger one — the 'once stopped, stays stopped' property that lets a *bound* on
halting time serve as a halting *test*."

NewDefinition Game.Complexity.haltTime Option Nat.Partrec.Code.evaln
NewTheorem Nat.Partrec.Code.evaln_complete Nat.Partrec.Code.evaln_mono Nat.find_spec
  Option.isSome_iff_exists Option.mem_def Part.dom_iff_mem dif_pos
