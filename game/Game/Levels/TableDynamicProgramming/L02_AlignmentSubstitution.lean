import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 2
Title "Alignment Substitution"

Introduction "The alignment specification records the cost of editing one list
into another. If two tails already align at cost `cost`, substituting one new
head symbol for another gives an alignment at cost `cost + 1`."

/-- A substitution step extends an existing alignment and increases cost by one. -/
Statement {α : Type} (a b : α) {xs ys : List α} {cost : Nat}
    (h : AlignmentCost xs ys cost) :
    AlignmentCost (a :: xs) (b :: ys) (cost + 1) := by
  Hint "`AlignmentCost` is inductive. Use its substitution constructor on the
  alignment of the tails."
  exact AlignmentCost.substitute a b h

Conclusion "Substitution is now registered as one step in an edit alignment."

NewTactic exact
NewDefinition Game.TableDP.AlignmentCost
NewTheorem Game.TableDP.AlignmentCost.substitute
