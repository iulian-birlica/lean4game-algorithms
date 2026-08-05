import Game.Levels.Introduction
import Game.Levels.StructuralInduction
import Game.Levels.Asymptotics

Title "The Algorithm Analysis Game"
Introduction "Welcome to the Algorithm Archive. Every routine you meet here
comes from a real algorithm-analysis course — verified once already in Lean,
and now yours to re-verify. Start in Introduction to pick up the tactics
you'll need, then follow the branch that matches the concept you want to
practice: contracts, design proofs, and asymptotics."

Info "The Algorithm Analysis Game.

Built on the [lean4game](https://github.com/leanprover-community/lean4game)
engine (the same engine behind the Natural Number Game). Levels are ported
from an algorithm-analysis course whose lemmas were originally proved with the
Aristotle tool.

Milestone 1: Introduction + the contract branches."

Languages "en"
CaptionShort "Algorithm Analysis Game"
CaptionLong "Prove correctness, cost, and complexity of classic algorithms in Lean 4."

Dependency Intro → StructuralInduction
Dependency Intro → Asymptotics

MakeGame
