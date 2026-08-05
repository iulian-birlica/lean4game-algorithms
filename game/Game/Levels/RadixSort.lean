import Game.Levels.RadixSort.L01_BitPassPerm
import Game.Levels.RadixSort.L02_RadixSortPerm
import Game.Levels.RadixSort.L03_BitPassStep
import Game.Levels.RadixSort.L04_RadixSortKey
import Game.Levels.RadixSort.L05_RadixSortSorted
import Game.Levels.RadixSort.L06_RadixSortCorrect

World "RadixSort"
Title "Radix Sort"

Introduction "Leave the world of comparison sorts. Radix sort never compares two
elements — it sorts by inspecting one bit at a time, least-significant bit first.
It is built from two functions: `bitPass`, one stable distribution by a single
bit, and `binaryRadixSort`, which applies `bitPass` across the bits. Prove that it
rearranges its input and, given enough bits, sorts it. Remarkably, it ends at the
very same specification as insertion and selection sort — a sorted permutation of
the input — which is the launching point for unifying what all these sorts have
in common."
