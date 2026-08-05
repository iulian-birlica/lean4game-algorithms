import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 8
Title "Memoization and Tabulation"

Introduction "Memoized and tabulated DP implementations are the same table when
they agree at every index. Prove that this pointwise specification is exactly
ordinary function equality."

/-- Pointwise equality of two DP tables is equivalent to function equality. -/
Statement {ι α : Type} (memo tabulation : ι → α) :
    SameTable memo tabulation ↔ memo = tabulation := by
  Hint "Unfold `SameTable`. For the forward direction, use `funext`; for the
  reverse direction, replace one table by the other."
  unfold SameTable
  constructor
  · intro h
    funext i
    exact h i
  · intro h
    subst tabulation
    intro i
    rfl

Conclusion "Memoization and tabulation now share the same extensional table contract."

NewTactic constructor exact funext intro rfl subst unfold
NewDefinition Game.TableDP.SameTable
