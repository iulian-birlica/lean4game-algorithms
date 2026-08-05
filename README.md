# Verified algorithms course in Lean 4

This repository is a worked algorithms course organized around machine-checked preconditions, postconditions, invariants, correctness proofs, and cost analyses.

## Start here

The lessons now live under `Game/Game/Levels/`; their numbers match the intended linear reading order:

1. specifications and proof foundations;
2. greedy algorithms, dynamic programming, and string matching;
3. asymptotic analysis, sorting, and amortized analysis;
4. proof automation, complexity theory, and computability.

`Game/Game/Support/TimeM.lean` is shared cost-model infrastructure. Completed design and planning documents are preserved in `docs/archive/`.

## Building

The project uses Lean 4 and Mathlib through Lake:

```sh
cd Game && lake build
```

The lab files contain complete reference proofs. They can also be turned into student worksheets by replacing selected proof bodies with exercises.
