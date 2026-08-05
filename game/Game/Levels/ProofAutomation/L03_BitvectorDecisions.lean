import Game.Metadata

World "ProofAutomation"
Level 3
Title "Bitvector Decisions"
-- source: RequestProject Lab18.and_self_bv, Lab18.xor_self_bv, Lab18.demorgan_bv,
--   Lab18.shift_left_one_bv, Lab18.clear_lowest_bit_submask

Introduction "`bv_decide` is different in kind from `aesop`/`grind`: for goals about
fixed-width bit-vectors (`BitVec w`) it *bit-blasts* the statement into a SAT problem, calls a
solver, and checks the certificate in the kernel — a genuine, total decision procedure for the
supported fragment. Prove five bitwise facts, from idempotence and De Morgan through the
'clear the lowest set bit' identity behind the classic population-count loop."

Statement (x : BitVec 8) (y z : BitVec 16) :
    x &&& x = x ∧
    x ^^^ x = 0#8 ∧
    (~~~(y &&& z) = (~~~y) ||| (~~~z)) ∧
    x <<< 1 = x * 2 ∧
    x &&& (x - 1) &&& x = x &&& (x - 1) := by
  Hint "Each conjunct is a decidable statement about fixed-width bit-vectors — `bv_decide`
  bit-blasts it to SAT and checks the resulting certificate."
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

Conclusion "Verified: idempotence, De Morgan, shift-as-multiply, and the lowest-set-bit
identity, each decided outright by `bv_decide`."

NewTactic bv_decide
