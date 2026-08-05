import Game.Levels.InsertionSort.L01_InsertPerm
import Game.Levels.InsertionSort.L02_InsertLowerBound
import Game.Levels.InsertionSort.L03_InsertSortedBase
import Game.Levels.InsertionSort.L04_InsertSortedHead
import Game.Levels.InsertionSort.L05_InsertSortedTail
import Game.Levels.InsertionSort.L06_InsertSortedStep
import Game.Levels.InsertionSort.L07_InsertSorted
import Game.Levels.InsertionSort.L08_InsertCorrect
import Game.Levels.InsertionSort.L09_InsertionSortPerm
import Game.Levels.InsertionSort.L10_InsertionSortSorted
import Game.Levels.InsertionSort.L11_InsertionSortCorrect
import Game.Levels.InsertionSort.L12_InsertLength
import Game.Levels.InsertionSort.L13_InsertionSortLength
import Game.Levels.InsertionSort.L14_InsertionSortMem
import Game.Levels.InsertionSort.L15_InsertCost
import Game.Levels.InsertionSort.L16_InsertCostSorted
import Game.Levels.InsertionSort.L17_InsertionSortCost

World "InsertionSort"
Title "Insertion Sort"

Introduction "Develop functional insertion sort in stages. First verify the
insertion helper and its invariants, splitting the sortedness proof into its
base case and the two branches of its inductive step. Then prove that the
complete sort is a sorted permutation of its input, and finish by analysing the
quadratic comparison bound."
