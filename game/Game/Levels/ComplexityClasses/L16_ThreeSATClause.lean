import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 16
Title "A Satisfiable 3-Clause"
-- source: ../game/Game/Worlds/W07Complexity/L07ThreeSATClause.lean

Introduction "A 3-CNF formula is a list of three-literal clauses. A clause containing one
positive literal is satisfiable under the all-true assignment, regardless of the other two
literals."

Statement (name other₁ other₂ : Nat) :
    Satisfiable3
      [({ name := name, positive := true },
        { name := other₁, positive := false },
        { name := other₂, positive := false })] := by
  Hint "Use the all-true assignment and unfold `evalCNF3`, `evalClause3`, and `Literal.eval`."
  exact ⟨fun _ => true, by simp [evalCNF3, evalClause3, Literal.eval]⟩

Conclusion "Verified: the sample 3-clause is satisfiable."

NewDefinition Game.Complexity.Literal Game.Complexity.Literal.eval Game.Complexity.Clause3
  Game.Complexity.CNF3 Game.Complexity.evalClause3 Game.Complexity.evalCNF3
  Game.Complexity.Satisfiable3
