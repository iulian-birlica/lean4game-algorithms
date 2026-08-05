import Game.Metadata

World "ProofAutomation"
Level 4
Title "XOR Swap Correctness"
-- source: RequestProject Lab18.xor_swap_fst, Lab18.xor_swap_snd

Introduction "The in-place **XOR swap** exchanges two words without a temporary: from
`(x, y)`, compute `a = x ^^^ y`, then `a ^^^ y` (which should recover `x`) and
`a ^^^ (a ^^^ y)` (which should recover `y`). Prove both halves recover the intended
values, on all `2^32` inputs — the completion prompt: which of `aesop`/`grind`/`bv_decide`
was suited to which lab, and why? (A reflection question, not a fourth theorem — the
kernel-checked proof below already answers 'why trust `bv_decide`': it is a total decision
procedure, not a heuristic search.)"

Statement (x y : BitVec 32) :
    (x ^^^ y) ^^^ ((x ^^^ y) ^^^ y) = y ∧ (x ^^^ y) ^^^ y = x := by
  Hint "Both halves are decidable bit-vector equalities — `bv_decide` settles each outright."
  refine ⟨?_, ?_⟩ <;> bv_decide

Conclusion "Verified: the XOR swap is provably correct, on every 32-bit input. Automation
Proof automation complete — `aesop` for logical search, `grind` for arithmetic-plus-case-analysis, and
`bv_decide` for total, checkable bit-vector decisions."
