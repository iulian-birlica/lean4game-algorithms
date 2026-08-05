import GameServer

/-! Tactic documentation shown in the inventory. Covers every tactic introduced
across the Academy and Contracts worlds. -/

/-- Closes a goal `a = a` (or any goal true by definitional/computational
unfolding) by checking both sides reduce to the same normal form. -/
TacticDoc rfl in "Basic"

/-- Introduces the hypothesis of an implication or the bound variable of a
`∀`-goal into the local context. -/
TacticDoc intro in "Basic"

/-- Closes the goal by providing a term that proves it exactly. -/
TacticDoc exact in "Basic"

/-- Splits a goal built from a constructor (e.g. `∧`, `↔`, `∃`) into one
subgoal per argument of that constructor. -/
TacticDoc constructor in "Construct"

/-- Rewrites the goal (or a hypothesis) using an equation or iff, left-to-right
by default; use `rw [← h]` to rewrite right-to-left. -/
TacticDoc rw in "Rewrite"

/-- Splits the proof into two cases: the given proposition holds, or its
negation holds. -/
TacticDoc by_cases in "Induction"

/-- Proves a `∨`-goal by proving its left disjunct. -/
TacticDoc left in "Construct"

/-- Proves a `∨`-goal by proving its right disjunct. -/
TacticDoc right in "Construct"

/-- Performs induction on a natural number, naming the induction hypothesis in
the successor case. -/
TacticDoc induction' in "Induction"

/-- Replaces a `def`-introduced name with its underlying definition. -/
TacticDoc unfold in "Rewrite"

/-- Like `exact`, but lets you leave some subterms as new goals (`?_`) to fill
in afterwards. -/
TacticDoc refine in "Construct"

/-- The older form of `refine`, with slightly different elaboration order for
metavariables — occasionally needed when `refine` fails to unify eagerly
enough. -/
TacticDoc refine' in "Construct"

/-- Destructures a term (an existential, a conjunction, a subtype, …) into
new named hypotheses in one step. -/
TacticDoc obtain in "Destruct"

/-- Applies a function or implication to the goal, leaving its arguments as
new goals. -/
TacticDoc apply in "Basic"

/-- Proves equality between functions by introducing an arbitrary input and
reducing the goal to equality of the two outputs at that input. -/
TacticDoc funext in "Basic"

/-- Introduces a hypothesis and immediately destructures it (pattern-matches
on `⟨⟩`, `∨`, etc.) in one step. -/
TacticDoc rintro in "Destruct"

/-- Destructures an existing hypothesis (pattern-matches on `⟨⟩`, `∨`, etc.). -/
TacticDoc rcases in "Destruct"

/-- Introduces a new hypothesis, proved by a side proof, into the local
context. -/
TacticDoc «have» in "Basic"

/-- Performs structural induction (or induction via a custom `.induct`
principle, with `using`), giving one case per constructor/branch with a
named induction hypothesis for each recursive occurrence. -/
TacticDoc induction in "Induction"

/-- Splits a goal into one case per constructor of the scrutinee's type,
without adding an induction hypothesis (no recursion). -/
TacticDoc cases in "Induction"

/-- Splits on the branches of a `match`/`if` appearing in the goal. -/
TacticDoc split in "Induction"

/-- Names the anonymous hypotheses most recently introduced (e.g. by
`split` or `rcases`) so they can be referred to explicitly. -/
TacticDoc rename_i in "Destruct"

/-- Uses an equality hypothesis to replace one side everywhere, removing the
now-redundant variable or hypothesis from the context. -/
TacticDoc subst in "Rewrite"

/-- Replaces the goal with a definitionally equal one stated explicitly —
useful for unfolding notation or `if`/`match` terms before rewriting. -/
TacticDoc «show» in "Basic"

/-- A decision procedure for linear arithmetic over `ℕ`/`ℤ`. -/
TacticDoc omega in "Arith"

/-- A decision procedure for commutative (semi)ring equalities. -/
TacticDoc ring in "Arith"

/-- Closes goals that are true by numerical computation (arithmetic
literals, simple inequalities). -/
TacticDoc norm_num in "Arith"

/-- Simplifies the goal using a given, exact list of lemmas (`simp only
[...]`) — like several `rw`s at once, but each lemma may apply anywhere it
matches, repeatedly. -/
TacticDoc simp in "Rewrite"

/-- Like `simp`, but also simplifies every hypothesis in the local context,
not just the goal. -/
TacticDoc simp_all in "Rewrite"

/-- A decision procedure for propositional logic (splitting on `∧`/`∨`/`↔`
and using hypotheses directly, without arithmetic). -/
TacticDoc tauto in "Search"

/-- Splits every `if`/`ite` appearing in the goal (and, with `at`, in a
hypothesis) into its two branches, one case per condition. -/
TacticDoc split_ifs in "Induction"

/-- Like `cases`, but accepts an anonymous-constructor pattern (`⟨_, _⟩`) to
name the new hypotheses inline. -/
TacticDoc cases' in "Destruct"

/-- A nonlinear extension of `linarith`: closes goals that follow from linear
arithmetic over an ordered field together with the products of given terms. -/
TacticDoc nlinarith in "Arith"

/-- A general-purpose proof search tactic: tries a configurable library of
lemmas and rules (`simp`-like rewriting, safe/unsafe rules) to close the
goal automatically. -/
TacticDoc aesop in "Search"

/-- Provides an explicit witness for an existential (or the components of an
anonymous constructor), leaving the remaining conditions as new goals. -/
TacticDoc use in "Construct"

/-- Puts the goal into a normal form for ring expressions without trying to
close it — useful to align both sides before a final `linarith`/`nlinarith`. -/
TacticDoc ring_nf in "Arith"

/-- `simpa [lemmas] using e` simplifies both the goal and the term `e`, then
checks that the simplified `e` closes the simplified goal. -/
TacticDoc simpa in "Rewrite"

/-- A decision procedure for goals of the form `0 < e`/`0 ≤ e`/`e ≠ 0`,
built from the sign/positivity of `e`'s subterms. -/
TacticDoc positivity in "Arith"

/-- Normalizes numeric casts between types (e.g. `ℕ`/`ℤ`/`ℝ`) so a goal
stated with mixed coercions matches a lemma or hypothesis stated without
them. -/
TacticDoc norm_cast in "Arith"

/-- Closes a goal that is true by a trivial/definitional fact (a mix of
`rfl`, `assumption`, and a few other simple closers). -/
TacticDoc trivial in "Search"

/-- Term-mode: `show P from proof` restates the goal as `P` (checked
definitionally equal) and closes it with `proof`. -/
TacticDoc «from» in "Term mode"

/-- Like `decide`, but evaluates via the compiler instead of the kernel
reducer — much faster for concrete numeric computations, at the cost of
trusting the compiler. -/
TacticDoc native_decide in "Search"

/-- Monadic-computation notation: sequences binder statements (`let`,
`←`, plain expressions) into a single value of a monad, used here to write
`TimeM` computations directly. -/
TacticDoc «do» in "Term mode"

/-- Term-mode: `mod_cast e` inserts the numeric casts needed to make `e`'s
type match the expected one — the term-mode counterpart of the
`exact_mod_cast`/`norm_cast` tactics. -/
TacticDoc «mod_cast» in "Term mode"

/-- A heavier search engine than `aesop`: combines case-splitting,
congruence closure, and linear arithmetic, learning facts as it goes.
Shines on goals mixing arithmetic with case analysis. -/
TacticDoc grind in "Search"

/-- A complete decision procedure for goals about fixed-width bit-vectors
(`BitVec w`): bit-blasts the statement into a SAT problem, calls a
solver, and checks the resulting certificate in the kernel. -/
TacticDoc bv_decide in "Search"
