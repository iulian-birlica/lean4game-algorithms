import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "AmortizedAnalysis"
Level 6
Title "Dynamic Array"
-- source: RequestProject Lab17.Inv_append, Lab17.append_amortized, Lab17.dynArray_amortized

Introduction "A **resizable array** doubles its capacity (copying the old
contents) whenever an `append` would overflow. Tracking the invariant
`size ≤ capacity ≤ 2·size` keeps the banker's balance `2·size − capacity`
non-negative. Prove `append` preserves the invariant and has amortized
cost `≤ 3`, then assemble the whole-sequence bound via the banker's
method."

Statement {α : Type*} :
    (∀ (x : α) (s : DynArray α), DynArray.Inv s → DynArray.Inv (DynArray.append x s)) ∧
    (∀ (x : α) (s : DynArray α), DynArray.Inv s →
      (DynArray.appendCost x s : ℤ) + DynArray.bal (DynArray.append x s) ≤ 3 + DynArray.bal s) ∧
    (∀ (ops : List (DAOp α)),
      totalCostL daStep daCost ops (DynArray.empty : DynArray α) ≤ 3 * ops.length) := by
  Hint "Prove invariant preservation and the amortized bound first — both case on whether the
  append triggers a resize. The sequence bound then assembles from `bankers_method_seq_le`."
  have hinv : ∀ (x : α) (s : DynArray α), DynArray.Inv s → DynArray.Inv (DynArray.append x s) := by
    intro x s hs
    obtain ⟨h1, h2⟩ := hs
    have hsz : (DynArray.append x s).size = s.size + 1 := DynArray.size_append x s
    refine ⟨?_, ?_⟩ <;> rw [hsz] <;> unfold DynArray.append <;> split_ifs with hlt <;>
      simp only [] <;> omega
  have hamort : ∀ (x : α) (s : DynArray α), DynArray.Inv s →
      (DynArray.appendCost x s : ℤ) + DynArray.bal (DynArray.append x s) ≤ 3 + DynArray.bal s := by
    intro x s hs
    obtain ⟨h1, h2⟩ := hs
    have hsz : (DynArray.append x s).size = s.size + 1 := DynArray.size_append x s
    unfold DynArray.appendCost DynArray.bal
    rw [hsz]
    unfold DynArray.append
    split_ifs with hlt <;> simp only [] <;> push_cast <;> omega
  refine ⟨hinv, hamort, ?_⟩
  Hint (hidden := true) "`daStep` preserves the invariant by `hinv` (on `append`) or trivially
  (on `lookup`); feed that, `hamort`, and `DynArray.bal_nonneg` to `bankers_method_seq_le`."
  intro ops
  have hstep_inv : ∀ (op : DAOp α) (s : DynArray α), DynArray.Inv s → DynArray.Inv (daStep op s) := by
    intro op s hs
    cases op <;> simp [daStep, hinv, hs]
  have h_bankers : ∀ (ops : List (DAOp α)) (s : DynArray α) (hs : DynArray.Inv s),
      (totalCostL daStep daCost ops s : ℤ) ≤ 3 * ops.length + DynArray.bal s := by
    intro ops s hs
    convert bankers_method_seq_le daStep daCost DynArray.bal 3 DynArray.Inv hstep_inv
      (fun s hs => DynArray.bal_nonneg s hs) (fun op s hs => ?_) ops s hs using 1
    cases op <;> simp +decide [*]
    · convert hamort _ _ hs using 1
    · simp +decide [daCost, daStep]
  exact_mod_cast h_bankers ops DynArray.empty DynArray.Inv_empty |> le_trans <|
    add_le_of_nonpos_right <| by simp +decide [DynArray.bal]

Conclusion "Verified: the resizable array's append is amortized O(1)."

NewDefinition Game.Clockwork.DynArray Game.Clockwork.DynArray.size
  Game.Clockwork.DynArray.empty Game.Clockwork.DynArray.append
  Game.Clockwork.DynArray.appendCost Game.Clockwork.DynArray.Inv
  Game.Clockwork.DynArray.bal Game.Clockwork.DAOp Game.Clockwork.DAOp.append
  Game.Clockwork.DAOp.lookup Game.Clockwork.daStep Game.Clockwork.daCost Inv
NewTactic push_cast
NewTheorem Game.Clockwork.DynArray.size_append Game.Clockwork.DynArray.bal_nonneg
  Game.Clockwork.DynArray.Inv_empty Game.Clockwork.bankers_method_seq_le
  add_le_of_nonpos_right
