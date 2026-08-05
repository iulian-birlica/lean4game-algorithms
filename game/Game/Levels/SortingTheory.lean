import Game.Levels.SortingTheory.L01_SortingContractAndAgreement
import Game.Levels.SortingTheory.L02_InsertionSortIsSort
import Game.Levels.SortingTheory.L03_SelectionSortIsSort
import Game.Levels.SortingTheory.L04_DecisionTreeLeaves
import Game.Levels.SortingTheory.L05_ComparisonSortLowerBound

World "SortingTheory"
Title "Sorting Theory"

Introduction "After the concrete comparison sorts, unify the story. Package
correctness as the shared `IsSort` contract, register insertion and selection
sort as instances of that contract, prove that all correct sorts agree, and
finish with the decision-tree lower bound for comparison sorting."
