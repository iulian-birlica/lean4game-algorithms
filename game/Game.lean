import Game.Levels.Introduction
import Game.Levels.StructuralInduction
import Game.Levels.ProofEngineering
import Game.Levels.HoareTriples
import Game.Levels.HoareTripleExercises
-- import Game.Levels.Greedy
-- import Game.Levels.DynamicProgramming
-- import Game.Levels.Sequences
-- import Game.Levels.Strings
-- import Game.Levels.PrefixStrings
-- import Game.Levels.AdvancedStrings
-- import Game.Levels.Graphs
-- import Game.Levels.TableDynamicProgramming
-- import Game.Levels.GreedyExercises
-- import Game.Levels.DataStructures
-- import Game.Levels.AdvancedDataStructures
-- import Game.Levels.Asymptotics
-- import Game.Levels.TimedComputation
-- import Game.Levels.NumericAlgorithms
-- import Game.Levels.RandomizedAlgorithms
-- import Game.Levels.ApproximationAlgorithms
-- import Game.Levels.Recurrence
-- import Game.Levels.ComparisonSorts
-- import Game.Levels.InsertionSort
-- import Game.Levels.SelectionSort
-- import Game.Levels.MergeSort
-- import Game.Levels.SortingTheory
-- import Game.Levels.RadixSort
-- import Game.Levels.Heap
-- import Game.Levels.AmortizedAnalysis
-- import Game.Levels.ProofAutomation
-- import Game.Levels.ComplexityClasses
-- import Game.Levels.AdvancedComplexity
-- import Game.Levels.LowerBounds
-- import Game.Levels.Computability

Title "The Algorithm Analysis Game"
Introduction "Welcome to the Algorithm Archive. Every routine you meet here
comes from a real algorithm-analysis course — verified once already in Lean,
and now yours to re-verify. Start in Introduction to pick up the tactics
you'll need, then follow the branch that matches the concept you want to
practice: contracts, design proofs, asymptotics, automation, complexity, or
computability."

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
Dependency StructuralInduction → ProofEngineering
-- Dependency StructuralInduction → HoareTriples
Dependency HoareTriples → HoareTripleExercises

-- Detached for now:
-- Dependency Intro → Asymptotics
-- Dependency StructuralInduction → Sequences
-- Dependency Sequences → Strings
-- Dependency Strings → PrefixStrings
-- Dependency PrefixStrings → AdvancedStrings
-- Dependency StructuralInduction → Greedy
-- Dependency Greedy → DynamicProgramming
-- Dependency Greedy → GreedyExercises
-- Dependency StructuralInduction → Graphs
-- Dependency Graphs → GreedyExercises
-- Dependency DynamicProgramming → TableDynamicProgramming
-- Dependency Graphs → TableDynamicProgramming
-- Dependency Asymptotics → TimedComputation
-- Dependency HoareTriples → NumericAlgorithms
-- Dependency TimedComputation → NumericAlgorithms
-- Dependency TimedComputation → RandomizedAlgorithms
-- Dependency Greedy → ApproximationAlgorithms
-- Dependency ComplexityClasses → ApproximationAlgorithms
-- Dependency TimedComputation → Recurrence
-- Dependency Recurrence → ComparisonSorts
-- Dependency ComparisonSorts → InsertionSort
-- Dependency ComparisonSorts → SelectionSort
-- Dependency ComparisonSorts → MergeSort
-- Dependency TimedComputation → MergeSort
-- Dependency InsertionSort → SortingTheory
-- Dependency SelectionSort → SortingTheory
-- Dependency MergeSort → SortingTheory
-- Dependency SortingTheory → Heap
-- Dependency SortingTheory → RadixSort
-- Dependency Recurrence → AmortizedAnalysis
-- Dependency SortingTheory → ProofAutomation
-- Dependency AmortizedAnalysis → ProofAutomation
-- Dependency AmortizedAnalysis → DataStructures
-- Dependency Graphs → DataStructures
-- Dependency DataStructures → AdvancedDataStructures
-- Dependency TimedComputation → ComplexityClasses
-- Dependency ProofAutomation → ComplexityClasses
-- Dependency ComplexityClasses → Computability
-- Dependency ComplexityClasses → AdvancedComplexity
-- Dependency AdvancedComplexity → LowerBounds
-- Dependency SortingTheory → LowerBounds

MakeGame
