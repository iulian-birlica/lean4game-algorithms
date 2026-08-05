import Game.Metadata
import Game.Support.Induction

World "HoareTriples"
Level 7
Title "Constant Folding Correctness"
-- source: RequestProject Lab02.aval_asimpConst

Introduction "The foundry's constant-folding pass must never change what an
expression evaluates to. Prove it by structural induction on the
expression tree: one case per constructor of `AExp`."

Statement (a : Game.Induction.AExp) (s : Game.Induction.State) :
    Game.Induction.aval (Game.Induction.asimpConst a) s = Game.Induction.aval a s := by
  Hint "Induct on `a` — a leaf case for `const`/`var`, and a step case for `plus`
  with an induction hypothesis for each subtree."
  induction a with
  | const n => rfl
  | var x => rfl
  | plus a b iha ihb =>
    Hint (hidden := true) "Rewrite with `h`, then the induction hypotheses, then
    unfold `asimpConst` and `split` on its match."
    have h : Game.Induction.aval (a.plus b) s
        = Game.Induction.aval a s + Game.Induction.aval b s := rfl
    rw [h, ← iha, ← ihb, Game.Induction.asimpConst]
    split
    · rename_i hm hn
      rw [hm, hn]; rfl
    · rfl

Conclusion "Folded and verified: constant folding never changes the value."

NewTactic induction split rename_i
NewDefinition Game.Induction.AExp Game.Induction.State Game.Induction.aval
  Game.Induction.asimpConst
