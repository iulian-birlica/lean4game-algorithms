import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "AmortizedAnalysis"
Level 5
Title "Backup Stack Amortized Bound"
-- source: RequestProject Lab17.bStackOp_amortized, Lab17.backupStack_amortized

Introduction "A **backup stack** supports `push`, `pop`, and `backup k`
(CLRS's *multipop*: drop the top `k` elements, costing `min k size`). A
single `backup` can be expensive, but amortized it is free — an element
can only be removed once, and it was paid for when pushed. Prove the
per-operation bound (potential = size, amortized cost `≤ 2`), then
assemble the sequence bound."

Statement {α : Type*} :
    (∀ (op : BStackOp α) (s : List α), bCost op s + bPhi (bStep op s) ≤ 2 + bPhi s) ∧
    (∀ (ops : List (BStackOp α)), totalCostL bStep bCost ops ([] : List α) ≤ 2 * ops.length) := by
  Hint "Prove the per-operation bound first, by cases on `op`; the sequence bound then follows
  from `potential_method_seq_le` instantiated at the stack's own potential `bPhi`."
  have hop : ∀ (op : BStackOp α) (s : List α), bCost op s + bPhi (bStep op s) ≤ 2 + bPhi s := by
    intro op s
    cases op <;> simp +arith +decide [bCost, bStep, bPhi]
    omega
  refine ⟨hop, ?_⟩
  Hint (hidden := true) "Convert to `potential_method_seq_le`, supplying the trivial invariant
  (`True` everywhere) and `hop` for its per-operation hypothesis."
  intro ops
  convert potential_method_seq_le _ _ bPhi _ _ _ _ _ _ _ using 1
  exacts [fun _ => True, fun _ _ _ => trivial, fun _ _ _ => hop _ _, trivial]

Conclusion "Verified: the backup stack's multipop is amortized O(1)."

NewDefinition Game.Clockwork.BStackOp Game.Clockwork.BStackOp.push
  Game.Clockwork.BStackOp.pop Game.Clockwork.BStackOp.backup
  Game.Clockwork.bStep Game.Clockwork.bCost Game.Clockwork.bPhi True
NewTactic exacts
NewTheorem Game.Clockwork.potential_method_seq_le
