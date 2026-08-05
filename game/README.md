# The Algorithm Analysis Game

A [lean4game](https://github.com/leanprover-community/lean4game) (Natural
Number Game engine) built from the ported algorithm-analysis course source in
this repository. The game is split into focused worlds with one directory per
world:

- **Introduction** — tactic-tutorial levels (`rfl`, `intro`/`exact`,
  `constructor`, `rw`, `by_cases`, `induction'`).
- **Structural induction** — list, tree, and finite-set induction material
  from Lab 02, placed before the Hoare triple worlds.
- **Hoare triples** and **Hoare triple exercises** — contract-style
  correctness proofs, loop invariants, sorting passes, digit counting,
  subtractive gcd, and digital root correctness.
- **Asymptotics** — growth-rate notation directly after Introduction.
- **Greedy**, **Dynamic Programming**, **Sequences**, and **Strings** —
  algorithm-design proofs across continuous knapsack, 0/1 knapsack,
  coin change, LCS, optimal BSTs, Kadane's algorithm, and Rabin-Karp.
- **Recurrence**, **Sorting**, **Heap**, and **Amortized Analysis** — the
  cost-analysis and sorting material split across its component worlds:
  the Master Theorem, the `TimeM` cost monad, sorting algorithms'
  exact/asymptotic costs, the comparison-sort lower bound, radix sort,
  heapsort, and amortized analysis (potential/banker's methods, binary
  counter, backup stack, dynamic array).
- **Proof automation** — levels across Lab 18:
  auditing `aesop`, `grind`, and `bv_decide` — what each one actually
  automates, ending with the verified XOR swap.
- **Complexity**, **Advanced Complexity**, **Lower Bounds**, and
  **Computability** — polynomial-time reductions, P and NP,
  Tseitin encodings and chained completeness arguments, adversary/counting
  lower bounds and conditional `P = NP` barriers, computability, Rice's
  theorem, and Busy Beaver.

## Levelsets

Refactored so far:

- [x] Asymptotics
- [ ] Advanced Complexity
- [ ] Advanced Data Structures
- [ ] Advanced Strings
- [ ] Amortized Analysis
- [ ] Approximation Algorithms
- [ ] Comparison Sorts
- [ ] Complexity Classes
- [ ] Computability
- [ ] Data Structures
- [x] Dynamic Programming
- [ ] Graphs
- [x] Greedy
- [x] Greedy Exercises
- [ ] Heap
- [ ] Hoare Triple Exercises
- [ ] Hoare Triples
- [ ] Insertion Sort
- [x] Introduction
- [ ] Lower Bounds
- [ ] Merge Sort
- [ ] Numeric Algorithms
- [ ] Prefix Strings
- [ ] Proof Automation
- [ ] Proof Engineering
- [ ] Radix Sort
- [ ] Randomized Algorithms
- [ ] Recurrence
- [ ] Selection Sort
- [ ] Sequences
- [ ] Sorting Theory
- [ ] Strings
- [x] Structural Induction
- [ ] Table Dynamic Programming
- [ ] Timed Computation

After large refactors, run `lake build` before merging. Expected non-error
noise includes the pervasive i18n messages and a handful of existing lint
warnings in `Design`.

## Fresh-clone bootstrap

This package lives in `game/` and must be reachable as a sibling of a
`lean4game` checkout at `../lean4game`. The helper script below
sets up that layout and intentionally skips cloning example/template games
such as `Robo`, `NNG4`, and `GameSkeleton`.

```bash
./scripts/bootstrap-algorithmgame-deps.sh
cd game
lake update -R -Klean4game.local   # resolve deps; GameServer from ../lean4game/server
lake exe cache get                  # pull prebuilt Mathlib oleans (skips an hours-long build)
lake build                          # compiles the game and runs MakeGame
```

`lake build` should finish with **no errors** and no warnings other than the
pervasive `No translation (en) found` i18n noise (present even in
`../lean4game`'s own source — harmless until the game is translated).
Any other warning (missing tactic/theorem/definition docs, "no world
introducing X", a dependency-graph loop) means something needs fixing before
merging.

## Running the game locally

```bash
cd lean4game
npm install     # first time only, or after node_modules gets corrupted
npm start       # builds GameServer, starts the relay (port 8080) and Vite client (port 3000)
```

Open `http://localhost:3000/#/g/local/Game`. After editing any Lean
file under `game/Game/`, re-run `lake build` in `game/` and
reload the browser — no need to restart `npm start`.

If `node_modules` ends up with broken bin symlinks (a stray `npm start`
failing with `Cannot find module '../src/assert'` or similar), the fix is
`rm -rf node_modules client/node_modules && npm install` from
`lean4game/`.

## Renaming or reordering levels

This repo includes a local copy of `sofi.sh` at repo root for bulk
renumbering/reordering inside a single world. Rename the level files in the
target world so their alphabetical order matches the intended in-game order,
then run:

```bash
./sofi.sh game/Game/Levels/<World>
```

The script will rename active level files to `L01_...`, `L02_...`, ...,
update each file's `Level N`, fix imports of previous levels in the same
world, and rewrite `game/Game/Levels/<World>.lean`.

## Adding a level

1. Pick the next theorem from the original course source for the world you're
   extending.
2. If it needs new answer-free definitions, add them to
   `game/Support/<World>.lean` with a `/-- ... -/` docstring on each — Lean's
   own docstrings satisfy the engine's documentation requirement without a
   separate `DefinitionDoc`/`TheoremDoc` entry, as long as one exists.
3. Create `game/Levels/<World>/LNN_Name.lean`:
   - `import Game.Metadata` (+ `import Game.Support.<World>` if needed)
   - `World "<World>"`, `Level N`, `Title`, `Introduction`
   - `Statement <binders> : <goal> := by <full model proof>` with `Hint`s at
     the points a player would get stuck
   - `Conclusion`
   - `NewTactic`/`NewTheorem`/`NewDefinition` for anything the proof uses for
     the first time anywhere in the game (fully-qualified names)
4. Add the new file's import to `game/Levels/<World>.lean`, in level order.
5. `lake build`. Fix any warning it reports — it will tell you exactly which
   identifier needs a `NewTheorem`/`NewDefinition`, or (only for Mathlib
   lemmas with no docstring of their own) a `TheoremDoc`/`DefinitionDoc` entry
   in `game/Doc/`.
6. Reload the browser and play the level.

## Gotchas learned while building Milestones 1–6

- `have` (and any other Lean keyword used as a tactic name, e.g. `show`)
  must be escaped as `«have»`/`«show»` when passed to
  `NewTactic`/`TacticDoc`/`OnlyTactic` — otherwise it's a parse error, not
  a warning.
- `Hint "...{x}..."` can only reference variables already in the local
  context at that exact point in the proof — placing a hint before the
  `intro` that introduces `x` will fail to elaborate.
- The engine's inventory tracker (`collectUsedInventory`) only scans the
  tactic proof after `:=`, not the goal's type signature. A `by ...` proof
  term embedded inside a dependent type (see `Contracts/L03_Reverse.lean`)
  is not scanned, and identifiers that appear only in the signature (e.g. a
  binder's type) don't need a `NewDefinition`.
- Most Mathlib lemmas do **not** have docstrings, so `NewTheorem` on them
  usually produces a real warning, not just an info message — check
  `game/Doc/Theorems.lean` for the running list before assuming Mathlib's
  docs will cover a new lemma for free. Mathlib *definitions* fare much
  better (most already have docstrings).
- Auto-generated declarations — a function's `.induct` functional-induction
  principle, and constructors of an `inductive` (unless you add a `/-- -/`
  directly above each constructor line) — have nowhere to write an inline
  docstring. Use `DefinitionDoc Foo.induct as "Foo.induct" in "Category"`
  in `game/Doc/Theorems.lean` instead (same file as `TheoremDoc`/
  `TacticDoc`; `DefinitionDoc` just needs a preceding `/-- -/` comment).
- Generic core combinators reached via dot-notation on a relation (`.symm`,
  `.trans`) can surface as bare `symm`/`trans`/`Trans.trans` dependencies
  distinct from the specific lemma (e.g. `Nat.ModEq.trans`) you already
  declared — the engine resolves them through the general `Trans`/`symm`
  typeclass machinery, not just the specific instance.
- `split`'s hypothesis-naming behavior on a multi-way `match` isn't fully
  predictable from a ported proof's original `rename_i`/`cases` names —
  when porting an existing proof, check the actual reported goal state
  (the error shows exactly which hypotheses are anonymous, and whether
  pattern variables like `m`/`n` are already named or not) rather than
  assuming the source proof's hypothesis count carries over unchanged.
  This can go further than a naming mismatch: for `lcs_length_max` (Design
  Lab 07), the auto-generated `.induct` principle's *second* recursive
  hypothesis in a multi-way branch didn't reliably resolve via `rename_i`
  at all (it kept binding to unrelated context items — a stray
  `Decidable` instance, in one case). When a `rename_i`-based hypothesis
  proves genuinely unreliable across a few tries, don't keep guessing —
  rewrite the proof as an explicit `Nat.strong_induction_on` with manual
  case analysis instead; it's more verbose but every hypothesis is one you
  bound yourself.
- `NewTheorem`'s implementation resolves its argument via `getConstInfo`
  directly on the identifier as written — this bypasses `open`-based
  namespace resolution entirely (unlike ordinary tactic-proof elaboration,
  which does respect `open`). If a level file uses `open Game.<World>` for
  readability (worthwhile once proofs get as dense as Design'), any
  `New*`/doc-lookup command referencing that world's own theorems or
  definitions still needs the fully-qualified name
  (`Game.<World>.foo`), even though the proof body can use the bare name
  `foo` freely.
- Notation that's `scoped` to a namespace (e.g. `<+` for `List.Sublist`)
  needs `open List` wherever it's *written* — including in level files
  that state a sublist fact in their `Statement`, not just in the support
  module where the underlying theorem is proved. Easy to lose when porting
  just a theorem's statement and body without its source file's own
  `open` line.
- The per-file `lake build` warnings ("Missing Theorem/Definition
  Documentation") are a *different, shallower* check than the full-project
  `lake build`'s world-dependency check ("No world introducing X, but
  required by World"). The former only scans a level's tactic-proof
  surface syntax for identifiers a `New*` command attempted to introduce;
  the latter scans the level's fully *elaborated* proof term and
  `Statement` type — catching things like bare `List`/`Fin`/`Equiv.Perm`
  occurrences that only appear in a signature and therefore never show up
  in the syntax scan.
- A file with **two separate `NewDefinition` (or `NewTheorem`/`NewTactic`)
  lines silently honours only the last one** — the first line's
  identifiers stop counting toward the inventory, with no warning that
  anything was dropped. Always merge new identifiers into the existing
  line for that command rather than appending a fresh one.
- Multi-line tactic terms are **whitespace-sensitive in ways that can
  break variable scoping**, not just indentation style: splitting `...
  using\n    someFn (... n ...)` across two lines (where `n` is bound by
  an enclosing `fun n =>`) can produce `Unknown identifier n` in the
  continuation, because Lean's parser stops treating the second line as
  part of the same term. If a line-wrapped version of an otherwise
  verbatim, working proof fails with unexplained scoping errors, try
  putting the wrapped expression back on one line before assuming
  something structural changed.
- A world's own definition can **collide with an unrelated, identically-
  named Mathlib declaration living at the Lean root namespace** (not
  under any namespace) — e.g. a `Game.<World>.Foo` clashing with a
  `_root_.Foo` from some Mathlib area with nothing to do with the game.
  `open Game.<World>` then makes every bare use of `Foo` ambiguous
  ("Ambiguous term ... Possible interpretations: ..."). The fix is to
  rename the world's own definition (and everywhere it's used, level
  files and Support file alike) to something that doesn't collide, rather
  than trying to force qualification at every use site.
- **`grind` (with or without `+suggestions`) can behave differently
  depending on the ambient file/namespace it runs in**, even when the
  local proof state is identical — its heuristic search draws on a wider
  pool of visible lemmas than just the ones a `simp`-style bracket list
  would name. A `grind` call ported verbatim from a source file that
  builds a whole *lab* (or several labs merged into one combined Support
  file, as this port does for Complexity) can fail or explode into an
  unrelated case-space purely because the surrounding declarations
  differ from the original file's. When this happens, don't try to debug
  why the search misbehaves — replace it with a direct, deterministic
  proof term citing the specific lemmas needed (the two or three
  supporting facts `grind` was presumably finding on its own).
