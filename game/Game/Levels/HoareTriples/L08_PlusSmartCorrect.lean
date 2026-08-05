import Game.Metadata
import Game.Support.Induction

World "HoareTriples"
Level 8
Title "Smart Addition Correctness"
-- source: RequestProject Lab02.aval_plusSmart

Introduction "`plusSmart` is a peephole optimiser: it folds two constants
and drops a `+ 0` as it builds the tree. Show it agrees with `plus` on
every value — a case split on both operands, not an induction."

Statement (a b : Game.Induction.AExp) (s : Game.Induction.State) :
    Game.Induction.aval (Game.Induction.plusSmart a b) s
      = Game.Induction.aval a s + Game.Induction.aval b s := by
  Hint "Case-split on `a`, then on `b`, inside each branch."
  cases a with
  | const m =>
    cases b with
    | const n => rfl
    | var x =>
      Hint (hidden := true) "Restate the goal with `show`, then split on whether `m = 0`."
      show Game.Induction.aval
          (if m = 0 then Game.Induction.AExp.var x
            else (Game.Induction.AExp.const m).plus (Game.Induction.AExp.var x)) s = _
      by_cases hm : m = 0
      · rw [if_pos hm, hm]; show s x = 0 + s x; rw [zero_add]
      · rw [if_neg hm]; rfl
    | plus p q =>
      show Game.Induction.aval
          (if m = 0 then p.plus q
            else (Game.Induction.AExp.const m).plus (p.plus q)) s = _
      by_cases hm : m = 0
      · rw [if_pos hm, hm]
        show Game.Induction.aval (p.plus q) s = 0 + Game.Induction.aval (p.plus q) s
        rw [zero_add]
      · rw [if_neg hm]; rfl
  | var x =>
    cases b with
    | const n =>
      show Game.Induction.aval
          (if n = 0 then Game.Induction.AExp.var x
            else (Game.Induction.AExp.var x).plus (Game.Induction.AExp.const n)) s = _
      by_cases hn : n = 0
      · rw [if_pos hn, hn]; show s x = s x + 0; rw [add_zero]
      · rw [if_neg hn]; rfl
    | var y => rfl
    | plus p q => rfl
  | plus p q =>
    cases b with
    | const n =>
      show Game.Induction.aval
          (if n = 0 then p.plus q else (p.plus q).plus (Game.Induction.AExp.const n)) s = _
      by_cases hn : n = 0
      · rw [if_pos hn, hn]
        show Game.Induction.aval (p.plus q) s = Game.Induction.aval (p.plus q) s + 0
        rw [add_zero]
      · rw [if_neg hn]; rfl
    | var y => rfl
    | plus r t => rfl

Conclusion "Verified: the smart constructor is a drop-in replacement for `plus`."

NewTactic cases «show»
NewDefinition Game.Induction.plusSmart Game.Induction.AExp.const Game.Induction.AExp.var
NewTheorem zero_add add_zero if_pos if_neg
