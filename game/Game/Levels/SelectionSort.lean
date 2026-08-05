import Game.Levels.SelectionSort.L01_SelectPerm
import Game.Levels.SelectionSort.L02_SelectLe
import Game.Levels.SelectionSort.L03_SelectMin
import Game.Levels.SelectionSort.L04_SelectionSortPerm
import Game.Levels.SelectionSort.L05_SelectionSortSorted
import Game.Levels.SelectionSort.L06_SelectionSortCorrect

World "SelectionSort"
Title "Selection Sort"

Introduction "Develop functional selection sort, the other classic comparison
sort, in stages. It is built from two functions: `select`, which extracts the
minimum of a list while keeping the rest in order, and `selectionSort`, which
repeatedly applies `select`. First verify that `select` rearranges its input and
truly extracts a minimum; then prove that the complete sort is a sorted
permutation of its input. This mirrors the insertion-sort world exactly; the
shared `IsSort` contract is recorded later in Sorting Theory."
