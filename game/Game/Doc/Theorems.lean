import GameServer
import Game.Support.Graph
import Game.Support.TableDP
import Game.Support.GreedyExercises
import Game.Support.PrefixStrings
import Game.Support.AdvancedStrings
import Game.Support.DataStructures

/-! Theorem documentation for the Mathlib/core lemmas used by model proofs
that have no docstring of their own in Mathlib (as reported by `lake build`).
Lemmas that already carry a Mathlib docstring are left to auto-resolve. -/

/-- `0 ≤ a → 0 ≤ b → 0 ≤ a / b` (division is non-negative for non-negative
numerator and denominator). -/
TheoremDoc div_nonneg as "div_nonneg" in "Greedy"

/-- `a / b ≤ 1`, given `a ≤ b` and `0 ≤ b`. -/
TheoremDoc div_le_one_of_le₀ as "div_le_one_of_le₀" in "Greedy"

/-- `simp`'s reduction of an `if`/`ite` once its condition is decided. -/
TheoremDoc reduceIte as "reduceIte" in "Greedy"

/-- `(∀ _, p) ↔ True`, i.e. a vacuous universal is trivially true. -/
TheoremDoc implies_true as "implies_true" in "Greedy"

/-- `(∀ _, True) ↔ True`. -/
TheoremDoc forall_const as "forall_const" in "Greedy"

/-- `1 * a = a`. -/
TheoremDoc one_mul as "one_mul" in "Greedy"

/-- If `x ∈ xs` then `x ∈ y :: xs` for any `y`. -/
TheoremDoc List.mem_cons_of_mem as "mem_cons_of_mem" in "Lists and permutations"

/-- `x ∈ y :: ys ↔ x = y ∨ x ∈ ys`. -/
TheoremDoc List.mem_cons as "mem_cons" in "Data Structures"

/-- `a ≤ a` (reflexivity, as a simp/term-mode lemma). -/
TheoremDoc le_rfl as "le_rfl" in "Logic, order, and algebra"

/-- `(∀ x, x = a → p x) ↔ p a`, the "forall over an equality" simplification. -/
TheoremDoc forall_eq_or_imp as "forall_eq_or_imp" in "Logic, order, and algebra"

/-- `¬ (a ≤ b) ↔ b < a`. -/
TheoremDoc not_le as "not_le" in "Sorting"

/-- `(p ∨ True) ↔ True`. -/
TheoremDoc or_true as "or_true" in "Greedy"

/-- `(True ∨ p) ↔ True`. -/
TheoremDoc true_or as "true_or" in "Greedy"

/-- `a * 0 = 0`. -/
TheoremDoc MulZeroClass.mul_zero as "mul_zero" in "Greedy"

/-- Multiplying an inequality on the left by a non-negative factor preserves
`≤`. -/
TheoremDoc mul_le_mul_of_nonneg_left as "mul_le_mul_of_nonneg_left" in "Greedy"

/-- Cancels a shared non-zero factor: `a / b * b = a`, given `b ≠ 0`. -/
TheoremDoc div_mul_cancel₀ as "div_mul_cancel₀" in "Greedy"

/-- `a < b → a ≠ b` (in the direction giving the larger term nonzero relative
to the smaller). -/
TheoremDoc ne_of_gt as "ne_of_gt" in "Greedy"

/-- `a / b * c = a * c / b`. -/
TheoremDoc div_mul_eq_mul_div as "div_mul_eq_mul_div" in "Greedy"

/-- `List.Pairwise R (a :: l) ↔ (∀ b ∈ l, R a b) ∧ List.Pairwise R l`. -/
TheoremDoc List.pairwise_cons as "pairwise_cons" in "Greedy"

/-- A non-`⊤` element of `WithTop α` comes from some `a : α`. -/
TheoremDoc WithTop.ne_top_iff_exists as "ne_top_iff_exists" in "Logic, order, and algebra"

/-- `a ≤ a ⊔ b`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Dynamic Programming"

/-- `a ≤ 0 ↔ a = 0`, in a canonically ordered additive monoid. -/
TheoremDoc nonpos_iff_eq_zero as "nonpos_iff_eq_zero" in "Dynamic Programming"

/-- `0 - a = 0` (truncated subtraction). -/
TheoremDoc zero_tsub as "zero_tsub" in "Dynamic Programming"

/-- `0 ≤ a`, for any element of an order with a least element. -/
TheoremDoc zero_le as "zero_le" in "Dynamic Programming"

/-- `x ∈ l.filter p ↔ x ∈ l ∧ p x = true`. -/
TheoremDoc List.mem_filter as "mem_filter" in "Strings"

/-- `x ∈ List.range n ↔ x < n`. -/
TheoremDoc List.mem_range as "mem_range" in "Strings"

/-- `n < m + 1 ↔ n ≤ m`. -/
TheoremDoc Nat.lt_add_one_iff as "lt_add_one_iff" in "Strings"

/-- `decide p = true ↔ p`. -/
TheoremDoc decide_eq_true_eq as "decide_eq_true_eq" in "Strings"

/-- `(l ++ l').foldl f init = l'.foldl f (l.foldl f init)`. -/
TheoremDoc List.foldl_append as "foldl_append" in "Strings"

/-- `(x :: l).foldl f init = l.foldl f (f init x)`. -/
TheoremDoc List.foldl_cons as "foldl_cons" in "Strings"

/-- `([] : List α).foldl f init = init`. -/
TheoremDoc List.foldl_nil as "foldl_nil" in "Strings"

/-- `l <+ x :: l` (a list is a sublist of any single-element extension of
itself). -/
TheoremDoc List.sublist_cons_self as "sublist_cons_self" in "Sequences"

/-- Sublist is transitive. -/
TheoremDoc List.Sublist.trans as "Sublist.trans" in "Lists and permutations"

/-- `n ≤ 0 ↔ n = 0`. -/
TheoremDoc Nat.le_zero as "le_zero" in "Sequences"

/-- `min a b = a`, given `a ≤ b`. -/
TheoremDoc min_eq_left as "min_eq_left" in "Sequences"

/-- `min a b = b`, given `b ≤ a`. -/
TheoremDoc min_eq_right as "min_eq_right" in "Sequences"

/-- `n ≤ n + 1 ≤ m` follows from `n ≤ m`. -/
TheoremDoc Nat.le_succ_of_le as "le_succ_of_le" in "Sequences"

/-- `n ≤ n` (reflexivity, `Nat`-specific form). -/
TheoremDoc Nat.le_refl as "le_refl" in "Sequences"

/-- `([] : List α).sum = 0`. -/
TheoremDoc List.sum_nil as "sum_nil" in "Sequences"

/-- `(x :: l).sum = x + l.sum`. -/
TheoremDoc List.sum_cons as "sum_cons" in "Sequences"

/-- `(x :: l).take (n+1) = x :: l.take n`. -/
TheoremDoc List.take_succ_cons as "take_succ_cons" in "Sequences"

/-- If two filter predicates agree pointwise on the list, filtering by
either gives the same result. -/
TheoremDoc List.filter_congr as "filter_congr" in "Strings"

/-- `decide p = false`, given a proof of `¬ p`. -/
TheoremDoc decide_eq_false as "decide_eq_false" in "Strings"

/-- `(a && true) = a`. -/
TheoremDoc Bool.and_true as "and_true" in "Strings"

/-- `(a && false) = false`. -/
TheoremDoc Bool.and_false as "and_false" in "Strings"

/-- `n + (k+1) = (n + k) + 1`. -/
TheoremDoc Nat.add_succ as "add_succ" in "Introduction"

/-- `gcd a b` divides `a`. -/
TheoremDoc Nat.gcd_dvd_left as "gcd_dvd_left" in "Hoare triples"

/-- `gcd a b` divides `b`. -/
TheoremDoc Nat.gcd_dvd_right as "gcd_dvd_right" in "Hoare triples"

/-- Any common divisor of `a` and `b` divides `gcd a b`. -/
TheoremDoc Nat.dvd_gcd as "dvd_gcd" in "Hoare triples"

/-- Reversing a list preserves its length. -/
TheoremDoc List.length_reverse as "length_reverse" in "Hoare triples"

/-- Indexing a reversed list at `i` matches indexing the original from the
other end. -/
TheoremDoc List.getElem_reverse as "getElem_reverse" in "Hoare triples"

/-- Permutation is symmetric. -/
TheoremDoc List.Perm.symm as "Perm.symm" in "Hoare triples"

/-- `x :: l.erase x` is a permutation of `l`, when `x ∈ l`. -/
TheoremDoc List.perm_cons_erase as "perm_cons_erase" in "Hoare triples"

/-- Merge-sorting a list produces a permutation of the original. -/
TheoremDoc List.mergeSort_perm as "mergeSort_perm" in "Sorting"

/-- `≤` is total: for any `a, b`, either `a ≤ b` or `b ≤ a`. -/
TheoremDoc le_total as "le_total" in "Sorting"

/-- `decide p = true` follows from a proof of `p` (given decidability). -/
TheoremDoc decide_eq_true as "decide_eq_true" in "Strings"

/-- A proof that `decide p = true` yields a proof of `p`. -/
TheoremDoc of_decide_eq_true as "of_decide_eq_true" in "Logic and decisions"

/-- `(a || b) = true ↔ a = true ∨ b = true`. -/
TheoremDoc Bool.or_eq_true_iff as "or_eq_true_iff" in "Logic and decisions"

/-- `x ∈ a.toList ↔ ∃ i (h : i < a.size), a[i] = x`. -/
TheoremDoc Array.mem_toList_iff as "mem_toList_iff" in "Hoare triples"

/-- `x ∈ a ↔ ∃ i (h : i < a.size), a[i] = x`. -/
TheoremDoc Array.mem_iff_getElem as "mem_iff_getElem" in "Hoare triples"

/-- `0 ≤ n` for every natural number. -/
TheoremDoc Nat.zero_le as "zero_le" in "Hoare triples"

/-- `0 + n = n`. -/
TheoremDoc Nat.zero_add as "zero_add" in "Greedy Exercises"

/-- `0 + a = a`, in any additive monoid. -/
TheoremDoc zero_add as "zero_add" in "Hoare triples"

/-- `a + 0 = a`, in any additive monoid. -/
TheoremDoc add_zero as "add_zero" in "Hoare triples"

/-- `n + 0 = n`. -/
TheoremDoc Nat.add_zero as "add_zero" in "Structural induction"

/-- `a ^ 0 = 1`. -/
TheoremDoc pow_zero as "pow_zero" in "Structural induction"

/-- Raising both sides of `a ≤ b` to the same power preserves `≤` (for a
monotone base). -/
TheoremDoc Nat.pow_le_pow_right as "pow_le_pow_right" in "Structural induction"

/-- `a ≤ max a b`. -/
TheoremDoc le_max_left as "le_max_left" in "Structural induction"

/-- `b ≤ max a b`. -/
TheoremDoc le_max_right as "le_max_right" in "Structural induction"

/-- `a < b` implies `a ≤ b`. -/
TheoremDoc le_of_lt as "le_of_lt" in "Sorting"

/-- `¬ (a < b) ↔ b ≤ a`. -/
TheoremDoc not_lt as "not_lt" in "Logic, order, and algebra"

/-- The empty range `Finset.range 0` is empty. -/
TheoremDoc Finset.range_zero as "range_zero" in "Exercises"

/-- `∑ k ∈ range (n+1), f k = (∑ k ∈ range n, f k) + f n`. -/
TheoremDoc Finset.sum_range_succ as "sum_range_succ" in "Exercises"

/-- The sum over the empty set is `0`. -/
TheoremDoc Finset.sum_empty as "sum_empty" in "Structural induction"

/-- `∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x`, when `a ∉ s`. -/
TheoremDoc Finset.sum_insert as "sum_insert" in "Structural induction"

/-- `Finset.induction_on`: every set is `∅`, or `insert a s` for a smaller
`s` with `a ∉ s` — the induction principle for finite sets in Lean. -/
TheoremDoc Finset.induction_on as "induction_on" in "Structural induction"

/-- If every element belongs to a finite set, then that set is `Finset.univ`. -/
TheoremDoc Finset.eq_univ_of_forall as "eq_univ_of_forall" in "Lower Bounds"

/-- A finite set has card greater than `1` iff it contains two distinct
elements. -/
TheoremDoc Finset.one_lt_card as "one_lt_card" in "Lower Bounds"

/-- The empty list has length `0`. -/
TheoremDoc List.length_nil as "length_nil" in "Structural induction"

/-- Cardinality is monotone under an injective map between finite types. -/
TheoremDoc Fintype.card_le_of_injective as "card_le_of_injective" in "Lower Bounds"

/-- The cardinality of a finite function type is the product of the
cardinalities of its codomains. -/
TheoremDoc Fintype.card_pi as "card_pi" in "Lower Bounds"

/-- `¬ (∀ x, p x)` yields an element with `¬ p x`. -/
TheoremDoc not_forall as "not_forall" in "Logic, order, and algebra"

/-- Reachability along relation `r` remains valid along any larger relation
`r'` containing every `r`-step. -/
TheoremDoc Relation.ReflTransGen.mono as "ReflTransGen.mono" in "Advanced"

/-- `(x :: l).length = l.length + 1`. -/
TheoremDoc List.length_cons as "length_cons" in "Sorting"

/-- The base-10 digit-unfolding equation: `digits 10 n = n % 10 :: digits
10 (n / 10)`, for `n > 0`. -/
TheoremDoc Nat.digits_def' as "digits_def'" in "Exercises"

/-- `Nat.digits b 0 = []`. -/
TheoremDoc Nat.digits_zero as "digits_zero" in "Exercises"

/-- `gcd 0 b = b`. -/
TheoremDoc Nat.gcd_zero_left as "gcd_zero_left" in "Exercises"

/-- `gcd a 0 = a`. -/
TheoremDoc Nat.gcd_zero_right as "gcd_zero_right" in "Exercises"

/-- `gcd a a = a`. -/
TheoremDoc Nat.gcd_self as "gcd_self" in "Exercises"

/-- `gcd (a - b) b = gcd a b`, when `b ≤ a`. -/
TheoremDoc Nat.gcd_sub_self_left as "gcd_sub_self_left" in "Exercises"

/-- `gcd a (b - a) = gcd a b`, when `a ≤ b`. -/
TheoremDoc Nat.gcd_sub_self_right as "gcd_sub_self_right" in "Natural numbers"

/-- Summing the base-`b` digits of `n` is congruent to `n` modulo `b - 1`
(here `b = 10`, modulus `9`). -/
TheoremDoc Nat.modEq_digits_sum as "modEq_digits_sum" in "Exercises"

/-- `Nat.ModEq` is transitive. -/
TheoremDoc Nat.ModEq.trans as "ModEq.trans" in "Exercises"

/-- `n + 1 ≠ 0`. -/
TheoremDoc Nat.succ_ne_zero as "succ_ne_zero" in "Exercises"

/-- `0 < n + 1`. -/
TheoremDoc Nat.succ_pos as "succ_pos" in "Natural numbers"

/-- Simplifies `if h : c then a else b` (or `if c then a else b` with a proof
of `c`) to `a`. -/
TheoremDoc if_pos as "if_pos" in "Hoare triples"

/-- Simplifies `if c then a else b` to `b`, given a proof of `¬ c`. -/
TheoremDoc if_neg as "if_neg" in "Hoare triples"

/-- Generic transitivity: from `a ~ b` and `b ~ c`, concludes `a ~ c`, for any
relation with a registered `Trans` instance. -/
TheoremDoc trans as "trans" in "Logic, order, and algebra"

/-- Generic symmetry: from `a ~ b`, concludes `b ~ a`, for any relation with a
registered symmetry lemma. -/
TheoremDoc symm as "symm" in "Logic, order, and algebra"

/-- `bubblePass`'s functional-induction principle: one case per branch of its
definition, with a recursive hypothesis for each recursive call. -/
DefinitionDoc Game.Contracts.bubblePass.induct as "bubblePass.induct" in "Hoare triples"

/-- `countDigits`'s functional-induction principle: one case per branch of
its definition, with a recursive hypothesis for the recursive call. -/
DefinitionDoc Game.Contracts.countDigits.induct as "countDigits.induct" in "Hoare triples"

/-- `gcdSub`'s functional-induction principle: one case per branch of its
definition, with a recursive hypothesis for each recursive call. -/
DefinitionDoc Game.Contracts.gcdSub.induct as "gcdSub.induct" in "Hoare triples"

/-- `control`'s functional-induction principle: one case per branch of its
definition, with a recursive hypothesis for the recursive call. -/
DefinitionDoc Game.Contracts.control.induct as "control.induct" in "Hoare triples"

/-- `lcs`'s functional-induction principle: one case per branch of its
definition, with a recursive hypothesis for each recursive call. -/
DefinitionDoc Game.Design.lcs.induct as "lcs.induct" in "Sequences"

/-- The empty list is a sublist of any list. -/
TheoremDoc List.nil_sublist as "nil_sublist" in "Lists and permutations"

/-- `0 < a⁻¹ ↔ 0 < a`. -/
TheoremDoc inv_pos as "inv_pos" in "Logic, order, and algebra"

/-- `0 ≤ a → 0 ≤ a ^ n`. -/
TheoremDoc pow_nonneg as "pow_nonneg" in "Logic, order, and algebra"

/-- `0 < a → 0 < a ^ n`. -/
TheoremDoc pow_pos as "pow_pos" in "Logic, order, and algebra"

/-- A sum of non-negative terms is non-negative. -/
TheoremDoc Finset.sum_nonneg as "sum_nonneg" in "Finite sets and counting"

/-- `|a| = a`, given `0 ≤ a`. -/
TheoremDoc abs_of_nonneg as "abs_of_nonneg" in "Big-O"

/-- `1 ≤ x → 1 ≤ x ^ p` (real exponent). -/
TheoremDoc Real.one_le_rpow as "one_le_rpow" in "Big-O"

/-- `∑ i ∈ range (n+1), f i = f 0 + ∑ i ∈ range n, f (i+1)` (peeling off the
first term instead of the last). -/
TheoremDoc Finset.sum_range_succ' as "sum_range_succ'" in "Recurrence"

/-- `|a * b| = |a| * |b|`. -/
TheoremDoc abs_mul as "abs_mul" in "Big-O"

/-- Multiplying an inequality on the right by a non-negative factor
preserves `≤`. -/
TheoremDoc mul_le_mul_of_nonneg_right as "mul_le_mul_of_nonneg_right" in "Approximation Algorithms"

/-- `a ≤ a + b`, given `0 ≤ b`. -/
TheoremDoc le_add_of_nonneg_right as "le_add_of_nonneg_right" in "Big-O"

/-- `0 ≤ |a|`. -/
TheoremDoc abs_nonneg as "abs_nonneg" in "Big-O"

/-- `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`. -/
TheoremDoc abs_le as "abs_le" in "Big-O"

/-- `a * (b * c) = a * b * c`. -/
TheoremDoc mul_assoc as "mul_assoc" in "Big-O"

/-- `c * ∑ i ∈ s, f i = ∑ i ∈ s, c * f i`. -/
TheoremDoc Finset.mul_sum as "mul_sum" in "Recurrence"

/-- `a + (b + c) = a + b + c`. -/
TheoremDoc add_assoc as "add_assoc" in "Recurrence"

/-- `a ^ (n + 1) = a * a ^ n` (the "prime" orientation of `pow_succ`). -/
TheoremDoc pow_succ' as "pow_succ'" in "Recurrence"

/-- `simp`'s reduction of a natural-number subtraction between literals. -/
TheoremDoc Nat.reduceSubDiff as "reduceSubDiff" in "Natural numbers"

/-- `a - 0 = a` (truncated subtraction). -/
TheoremDoc tsub_zero as "tsub_zero" in "Logic, order, and algebra"

/-- `0 < b - a`, given `a < b`. -/
TheoremDoc Nat.sub_pos_of_lt as "sub_pos_of_lt" in "Natural numbers"

/-- `m / n = k`, given `0 < n` and `m = k * n`. -/
TheoremDoc Nat.div_eq_of_eq_mul_left as "div_eq_of_eq_mul_left" in "Recurrence"

/-- `l ~ [] ↔ l = []`: the empty list is the only permutation of itself. -/
TheoremDoc List.perm_nil as "perm_nil" in "Lists and permutations"

/-- `l ~ [a] ↔ l = [a]`: a singleton's only permutation is itself. -/
TheoremDoc List.perm_singleton as "perm_singleton" in "Lists and permutations"

/-- `(a :: l).filter p = a :: l.filter p`, given `p a`. -/
TheoremDoc List.filter_cons_of_pos as "filter_cons_of_pos" in "Lists and permutations"

/-- `(a :: l).filter p = l.filter p`, given `¬ p a`. -/
TheoremDoc List.filter_cons_of_neg as "filter_cons_of_neg" in "Lists and permutations"

/-- `(b :: l).count a = l.count a + (1 if b = a else 0)`. -/
TheoremDoc List.count_cons as "count_cons" in "Lists and permutations"

/-- `([] : List α).filter p = []`. -/
TheoremDoc List.filter_nil as "filter_nil" in "Lists and permutations"

/-- `a ≤ b → c ≤ d → a + c ≤ b + d`, for natural numbers. -/
TheoremDoc Nat.add_le_add as "add_le_add" in "Natural numbers"

/-- `a ≤ a ^ n`, given `n ≠ 0`. -/
TheoremDoc le_self_pow as "le_self_pow" in "Natural numbers"

/-- `0 < Real.log x`, given `1 < x`. -/
TheoremDoc Real.log_pos as "log_pos" in "Asymptotics"

/-- `Real.log x ≤ Real.log y`, given `0 < x` and `x ≤ y`. -/
TheoremDoc Real.log_le_log as "log_le_log" in "Asymptotics"

/-- `0 ≤ Real.log x`, given `1 ≤ x`. -/
TheoremDoc Real.log_nonneg as "log_nonneg" in "Asymptotics"

/-- `0.6931471803 < Real.log 2`, a rational lower bound. -/
TheoremDoc Real.log_two_gt_d9 as "log_two_gt_d9" in "Asymptotics"

/-- `Real.log 2 < 0.6931471808`, a rational upper bound. -/
TheoremDoc Real.log_two_lt_d9 as "log_two_lt_d9" in "Asymptotics"

/-- `2.7182818283 < Real.exp 1`, a rational lower bound on Euler's number. -/
TheoremDoc Real.exp_one_gt_d9 as "exp_one_gt_d9" in "Asymptotics"

/-- `x + 1 ≤ Real.exp x`, for every real `x`. -/
TheoremDoc Real.add_one_le_exp as "add_one_le_exp" in "Asymptotics"

/-- `x ≤ Nat.log b y`, given `1 < b` and `b ^ x ≤ y`. -/
TheoremDoc Nat.le_log_of_pow_le as "le_log_of_pow_le" in "Natural numbers"

/-- `b ^ Nat.log b x ≤ x`, given `x ≠ 0`. -/
TheoremDoc Nat.pow_log_le_self as "pow_log_le_self" in "Natural numbers"

/-- `(1 : α) < 2`. -/
TheoremDoc one_lt_two as "one_lt_two" in "Logic, order, and algebra"

/-- `[a].Pairwise R` holds unconditionally, for any relation `R`. -/
TheoremDoc List.pairwise_singleton as "pairwise_singleton" in "Sorting"

/-- `a ≤ b → c ≤ d → a + c ≤ b + d`, in any ordered additive structure. -/
TheoremDoc add_le_add as "add_le_add" in "Logic, order, and algebra"

/-- `a ^ m ≤ a ^ n`, given `1 ≤ a` and `m ≤ n`. -/
TheoremDoc pow_le_pow_right₀ as "pow_le_pow_right₀" in "Logic, order, and algebra"

/-- `s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t`. -/
TheoremDoc Finset.image_subset_iff as "image_subset_iff" in "Finite sets and counting"

/-- `(s.image f).card = s.card`, given `f` injective. -/
TheoremDoc Finset.card_image_of_injective as "card_image_of_injective" in "Finite sets and counting"

/-- `Fintype.card (Equiv.Perm α) = (Fintype.card α)!`. -/
TheoremDoc Fintype.card_perm as "card_perm" in "Finite sets and counting"

/-- `Finset.card` is monotone: `s ⊆ t → s.card ≤ t.card`. -/
TheoremDoc Finset.card_mono as "card_mono" in "Finite sets and counting"

/-- `a ^ (n + 1) = a ^ n * a`. -/
TheoremDoc pow_succ as "pow_succ" in "Numeric Algorithms"

/-- `(p ∧ True) ↔ p`. -/
TheoremDoc true_and as "true_and" in "Logic, order, and algebra"

/-- `(f <$> x).ret = f x.ret`: mapping over a `TimeM` computation applies `f` to its
return value. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.ret_map as "ret_map" in "Timed Computation"

/-- `(m >>= f).ret = (f m.ret).ret`: the return value of a bind is the return value
of the continuation applied to the first computation's return value. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.ret_bind as "ret_bind" in "Timed Computation"

/-- `(tick c).ret = ()`: a tick has no interesting return value. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.ret_tick as "ret_tick" in "Timed Computation"

/-- Permutations preserve membership: `l₁ ~ l₂ → l₁ ⊆ l₂`. -/
TheoremDoc List.Perm.subset as "Perm.subset" in "Sorting"

/-- Permutation is reflexive: `l ~ l`. -/
TheoremDoc List.Perm.refl as "Perm.refl" in "Sorting"

/-- Strong induction on `ℕ`: to prove `p n` for all `n`, it suffices to prove `p n`
assuming `p m` for every `m < n`. -/
TheoremDoc Nat.strong_induction_on as "strong_induction_on" in "Natural numbers"

/-- `(pure a : TimeM T α).time = 0`: a pure value costs no time. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.time_pure as "time_pure" in "Timed Computation"

/-- `(m >>= f).time = m.time + (f m.ret).time`: the time cost of a bind is the sum of
both computations' costs. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.time_bind as "time_bind" in "Timed Computation"

/-- `(tick c).time = c`: a tick's cost is exactly the amount charged. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.time_tick as "time_tick" in "Timed Computation"

/-- `(f <$> x).time = x.time`: mapping over a `TimeM` computation doesn't change its
time cost. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.time_map as "time_map" in "Timed Computation"

/-- `Real.log (x ^ n) = n * Real.log x`. -/
TheoremDoc Real.log_pow as "log_pow" in "Asymptotics"

/-- `0 * n = 0`. -/
TheoremDoc Nat.zero_mul as "zero_mul" in "Natural numbers"

/-- `l₁ ~ l₂ ↔ ∀ a, l₁.count a = l₂.count a`: permutation is equivalent
to agreeing on every element's count. -/
TheoremDoc List.perm_iff_count as "perm_iff_count" in "Lists and permutations"

/-- `(l.flatMap f).count x = (l.map (count x ∘ f)).sum`: counting `x` in a
flattened map is the sum of counting it in each piece. -/
TheoremDoc List.count_flatMap as "count_flatMap" in "Lists and permutations"

/-- If `f` vanishes on `l` except possibly at one point `a`, then
`(l.map f).sum = l.count a • f a` — a sum with at most one nonzero
term. -/
TheoremDoc List.sum_map_eq_nsmul_single as "sum_map_eq_nsmul_single" in "Lists and permutations"

/-- `a < b → ¬ b ≤ a`. -/
TheoremDoc not_le_of_gt as "not_le_of_gt" in "Lower Bounds"

/-- `l.count a = 0 ↔ a ∉ l`. -/
TheoremDoc List.count_eq_zero as "count_eq_zero" in "Lists and permutations"

/-- Weakens the relation of a `Pairwise` fact, given the weaker relation
holds pointwise among the list's own members. -/
TheoremDoc List.Pairwise.imp_of_mem as "Pairwise.imp_of_mem" in "Sorting"

/-- `a < b → a % b = a`. -/
TheoremDoc Nat.mod_eq_of_lt as "mod_eq_of_lt" in "Natural numbers"

/-- `l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a)`. -/
TheoremDoc List.pairwise_reverse as "pairwise_reverse" in "Lists and permutations"

/-- Permutations agree on membership: `l₁ ~ l₂ → (a ∈ l₁ ↔ a ∈ l₂)`. -/
TheoremDoc List.Perm.mem_iff as "Perm.mem_iff" in "Sorting"

/-- `x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂`. -/
TheoremDoc List.mem_append as "mem_append" in "Data Structures"

/-- `min a b ≤ a`. -/
TheoremDoc Nat.min_le_left as "min_le_left" in "Graphs"

/-- `min a b ≤ b`. -/
TheoremDoc Nat.min_le_right as "min_le_right" in "Graphs"

/-- `a = b → b ≤ c → a ≤ c`. -/
TheoremDoc le_of_eq_of_le as "le_of_eq_of_le" in "Logic, order, and algebra"

/-- `a ≥ b ↔ b ≤ a`. -/
TheoremDoc ge_iff_le as "ge_iff_le" in "Logic, order, and algebra"

/-- `n ≤ n + k`. -/
TheoremDoc Nat.le_add_right as "le_add_right" in "Amortized Analysis"

/-- `b ≤ 0 → a + b ≤ a`. -/
TheoremDoc add_le_of_nonpos_right as "add_le_of_nonpos_right" in "Logic, order, and algebra"

/-- `(pure a : TimeM T α).ret = a`: a pure value returns exactly `a`. -/
TheoremDoc Cslib.Algorithms.Lean.TimeM.ret_pure as "ret_pure" in "Timed Computation"

/-- A timed computation carrying a return value and an accumulated cost. -/
DefinitionDoc Cslib.Algorithms.Lean.TimeM as "TimeM" in "Timed Computation"

/-- The `TimeM` constructor: pairs a return value with its accumulated
time cost. -/
DefinitionDoc Cslib.Algorithms.Lean.TimeM.mk as "mk" in "Timed Computation"

/-- The return-value projection of a timed computation. -/
DefinitionDoc Cslib.Algorithms.Lean.TimeM.ret as "ret" in "Timed Computation"

/-- The accumulated-cost projection of a timed computation. -/
DefinitionDoc Cslib.Algorithms.Lean.TimeM.time as "time" in "Timed Computation"

/-- A timed computation that spends exactly the requested cost and returns
unit. -/
DefinitionDoc Cslib.Algorithms.Lean.TimeM.tick as "tick" in "Timed Computation"

/-- Extracts the real-valued cost function from a timed routine indexed by
input size. -/
DefinitionDoc Game.Clockwork.timeCost as "timeCost" in "Timed Computation"

/-- Applying a `timeCost` function returns the `.time` field of the indexed
timed computation. -/
TheoremDoc Game.Clockwork.timeCost_apply as "timeCost_apply" in "Timed Computation"

/-- A directed graph represented by its edge relation. -/
DefinitionDoc Game.Graph.DirectedGraph as "DirectedGraph" in "Graphs"

/-- Reachability from a fixed source through zero or more directed edges. -/
DefinitionDoc Game.Graph.Reach as "Reach" in "Graphs"

/-- Zero-edge reachability from a vertex to itself. -/
TheoremDoc Game.Graph.Reach.refl as "Reach.refl" in "Graphs"

/-- Extends a reachability proof across one outgoing edge. -/
TheoremDoc Game.Graph.Reach.tail as "Reach.tail" in "Graphs"

/-- Every vertex in a BFS queue has already been reached from the source. -/
DefinitionDoc Game.Graph.QueueInvariant as "QueueInvariant" in "Graphs"

/-- A path relation indexed by its edge count. -/
DefinitionDoc Game.Graph.PathLength as "PathLength" in "Graphs"

/-- A path-length certificate that no shorter path exists. -/
DefinitionDoc Game.Graph.IsShortest as "IsShortest" in "Graphs"

/-- A list order where every represented edge points forward. -/
DefinitionDoc Game.Graph.IsTopological as "IsTopological" in "Graphs"

/-- Mutual reachability, used as the SCC relation. -/
DefinitionDoc Game.Graph.StronglyConnected as "StronglyConnected" in "Graphs"

/-- One tentative-distance relaxation step. -/
DefinitionDoc Game.Graph.relax as "relax" in "Graphs"

/-- Floyd-Warshall's one-intermediate update. -/
DefinitionDoc Game.Graph.floydUpdate as "floydUpdate" in "Graphs"

/-- Whether an edge crosses a cut. -/
DefinitionDoc Game.Graph.CrossesCut as "CrossesCut" in "Graphs"

/-- A minimum-weight edge among all edges crossing a cut. -/
DefinitionDoc Game.Graph.IsLightCutEdge as "IsLightCutEdge" in "Graphs"

/-- Equality of union-find representatives. -/
DefinitionDoc Game.Graph.SameRepresentative as "SameRepresentative" in "Graphs"

/-- Relabels one union-find class to perform a union. -/
DefinitionDoc Game.Graph.unionLabels as "unionLabels" in "Graphs"

/-- One edit-distance table update, choosing among deletion, insertion, and
substitution candidates. -/
DefinitionDoc Game.TableDP.editUpdate as "editUpdate" in "Table Dynamic Programming"

/-- An explicit edit-alignment relation indexed by edit cost. -/
DefinitionDoc Game.TableDP.AlignmentCost as "AlignmentCost" in "Table Dynamic Programming"

/-- Empty lists align at zero cost. -/
TheoremDoc Game.TableDP.AlignmentCost.nil as "AlignmentCost.nil" in "Table Dynamic Programming"

/-- Matching equal symbols preserves the alignment cost. -/
TheoremDoc Game.TableDP.AlignmentCost.match as "AlignmentCost.match" in "Table Dynamic Programming"

/-- Deleting one source symbol increases the alignment cost by one. -/
TheoremDoc Game.TableDP.AlignmentCost.delete as "AlignmentCost.delete" in "Table Dynamic Programming"

/-- Inserting one target symbol increases the alignment cost by one. -/
TheoremDoc Game.TableDP.AlignmentCost.insert as "AlignmentCost.insert" in "Table Dynamic Programming"

/-- Substituting one symbol for another increases the alignment cost by one. -/
TheoremDoc Game.TableDP.AlignmentCost.substitute as "AlignmentCost.substitute" in "Table Dynamic Programming"

/-- Declarative specification for a successful subset-sum table entry. -/
DefinitionDoc Game.TableDP.HasSubsetSum as "HasSubsetSum" in "Table Dynamic Programming"

/-- A matrix-chain split candidate combines two subproblem costs with the
scalar multiplication cost at their boundary. -/
DefinitionDoc Game.TableDP.matrixSplitCost as "matrixSplitCost" in
  "Table Dynamic Programming"

/-- Improves a matrix-chain cell by keeping the cheaper of the current value
and a candidate split. -/
DefinitionDoc Game.TableDP.improveMatrixChain as "improveMatrixChain" in
  "Table Dynamic Programming"

/-- A Floyd-Warshall table layer allowing one more intermediate vertex. -/
DefinitionDoc Game.TableDP.floydLayer as "floydLayer" in "Table Dynamic Programming"

/-- A strictly increasing candidate list for longest increasing subsequence. -/
DefinitionDoc Game.TableDP.StrictlyIncreasing as "StrictlyIncreasing" in
  "Table Dynamic Programming"

/-- Pointwise equality between two DP table implementations. -/
DefinitionDoc Game.TableDP.SameTable as "SameTable" in "Table Dynamic Programming"

/-- An activity interval with a start and finish time. -/
DefinitionDoc Game.Greedy.Activity as "Activity" in "Greedy Exercises"

/-- The start time of an activity. -/
DefinitionDoc Game.Greedy.Activity.start as "Activity.start" in "Greedy Exercises"

/-- The finish time of an activity. -/
DefinitionDoc Game.Greedy.Activity.finish as "Activity.finish" in "Greedy Exercises"

/-- The relation saying one activity can be followed by another without overlap. -/
DefinitionDoc Game.Greedy.Compatible as "Compatible" in "Greedy Exercises"

/-- A candidate activity finishes no later than every activity in a list. -/
DefinitionDoc Game.Greedy.EarliestFinish as "EarliestFinish" in "Greedy Exercises"

/-- A pairwise-compatible activity schedule. -/
DefinitionDoc Game.Greedy.IsSchedule as "IsSchedule" in "Greedy Exercises"

/-- A binary Huffman tree with weighted leaves. -/
DefinitionDoc Game.Greedy.HuffmanTree as "HuffmanTree" in "Greedy Exercises"

/-- A Huffman-tree leaf storing one symbol weight. -/
DefinitionDoc Game.Greedy.HuffmanTree.leaf as "HuffmanTree.leaf" in "Greedy Exercises"

/-- A Huffman-tree internal node merging two subtrees. -/
DefinitionDoc Game.Greedy.HuffmanTree.node as "HuffmanTree.node" in "Greedy Exercises"

/-- The total symbol weight below a Huffman tree. -/
DefinitionDoc Game.Greedy.HuffmanTree.weight as "HuffmanTree.weight" in "Greedy Exercises"

/-- The weighted external path length of a Huffman tree at a starting depth. -/
DefinitionDoc Game.Greedy.HuffmanTree.externalCost as "HuffmanTree.externalCost" in
  "Greedy Exercises"

/-- The binary codewords generated by a Huffman tree. -/
DefinitionDoc Game.Greedy.HuffmanTree.codewords as "HuffmanTree.codewords" in
  "Greedy Exercises"

/-- The property that no codeword is a prefix of a distinct codeword. -/
DefinitionDoc Game.Greedy.PrefixFree as "PrefixFree" in "Greedy Exercises"

/-- Increasing every Huffman leaf depth by one adds the total tree weight. -/
TheoremDoc Game.Greedy.HuffmanTree.externalCost_succ as "HuffmanTree.externalCost_succ"
  in "Greedy Exercises"

/-- The codewords generated by a Huffman tree are prefix-free. -/
TheoremDoc Game.Greedy.HuffmanTree.prefixFree_codewords as
  "HuffmanTree.prefixFree_codewords" in "Greedy Exercises"

/-- A scheduled job with duration, deadline, and profit. -/
DefinitionDoc Game.Greedy.Job as "Job" in "Greedy Exercises"

/-- A job's processing time. -/
DefinitionDoc Game.Greedy.Job.duration as "Job.duration" in "Greedy Exercises"

/-- A job's deadline. -/
DefinitionDoc Game.Greedy.Job.deadline as "Job.deadline" in "Greedy Exercises"

/-- A job's profit. -/
DefinitionDoc Game.Greedy.Job.profit as "Job.profit" in "Greedy Exercises"

/-- The total processing time of a list of jobs. -/
DefinitionDoc Game.Greedy.scheduledTime as "scheduledTime" in "Greedy Exercises"

/-- The total profit of a list of jobs. -/
DefinitionDoc Game.Greedy.totalProfit as "totalProfit" in "Greedy Exercises"

/-- Deadline feasibility for a job list after some elapsed time. -/
DefinitionDoc Game.Greedy.MeetsDeadlines as "MeetsDeadlines" in "Greedy Exercises"

/-- The length of the common prefix of two symbol lists. -/
DefinitionDoc Game.String.commonPrefixLength as "commonPrefixLength" in "Prefix Strings"

/-- A word is a prefix when appending some remainder reconstructs the text. -/
DefinitionDoc Game.String.IsPrefix as "IsPrefix" in "Prefix Strings"

/-- A word is a suffix when prepending some remainder reconstructs the text. -/
DefinitionDoc Game.String.IsSuffix as "IsSuffix" in "Prefix Strings"

/-- A KMP border is simultaneously a prefix and a suffix. -/
DefinitionDoc Game.String.IsBorder as "IsBorder" in "Prefix Strings"

/-- The match length inspected by KMP at a candidate starting position. -/
DefinitionDoc Game.String.kmpMatchLength as "kmpMatchLength" in "Prefix Strings"

/-- A complete KMP match at a candidate starting position. -/
DefinitionDoc Game.String.KMPMatch as "KMPMatch" in "Prefix Strings"

/-- The Z value at a position: the common-prefix length of the whole text and
the suffix beginning there. -/
DefinitionDoc Game.String.zValue as "zValue" in "Prefix Strings"

/-- Abstract linear-scan accounting invariant for KMP. -/
DefinitionDoc Game.String.WithinKMPBudget as "WithinKMPBudget" in "Prefix Strings"

/-- A word is a prefix of another exactly when their common-prefix length
reaches the whole word. -/
TheoremDoc Game.String.commonPrefixLength_eq_length_iff_isPrefix as
  "commonPrefixLength_eq_length_iff_isPrefix" in "Prefix Strings"

/-- A finite trie, storing whether a word ends at each node and an optional
child per symbol. -/
DefinitionDoc Game.String.Trie as "Trie" in "Prefix Strings"

/-- The single trie constructor: a terminal flag plus an optional child per
symbol. -/
DefinitionDoc Game.String.Trie.node as "Trie.node" in "Prefix Strings"

/-- The empty prefix tree. -/
DefinitionDoc Game.String.Trie.empty as "Trie.empty" in "Prefix Strings"

/-- Membership lookup in a trie. -/
DefinitionDoc Game.String.Trie.lookup as "Trie.lookup" in "Prefix Strings"

/-- Insert one word into a trie, sharing its prefix with existing branches. -/
DefinitionDoc Game.String.Trie.insert as "Trie.insert" in "Prefix Strings"

/-- The suffix of a list beginning at a given position. -/
DefinitionDoc Game.AdvancedString.suffix as "suffix" in "Advanced"

/-- All valid suffix starting positions, including the empty suffix. -/
DefinitionDoc Game.AdvancedString.suffixIndices as "suffixIndices" in "Advanced"

/-- The suffixes of a list in original text order, including the empty
suffix. -/
DefinitionDoc Game.AdvancedString.suffixes as "suffixes" in "Advanced"

/-- A non-strict lexicographic relation induced by a strict symbol order. -/
DefinitionDoc Game.AdvancedString.LexLE as "LexLE" in "Advanced"

/-- The longest-common-prefix value used by suffix-array LCP tables. -/
DefinitionDoc Game.AdvancedString.lcp as "lcp" in "Advanced"

/-- A suffix-array certificate: every valid suffix position occurs exactly
once, and the listed suffixes are in lexicographic order. -/
DefinitionDoc Game.AdvancedString.IsSuffixArray as "IsSuffixArray" in "Advanced"

/-- A binary tree of natural-number keys, used as a search tree. -/
DefinitionDoc Game.DataStructures.SearchTree as "SearchTree" in "Data Structures"

/-- The empty search tree. -/
DefinitionDoc Game.DataStructures.SearchTree.nil as "SearchTree.nil" in "Data Structures"

/-- A search-tree node: a left subtree, a key, and a right subtree. -/
DefinitionDoc Game.DataStructures.SearchTree.node as "SearchTree.node" in "Data Structures"

/-- Dictionary lookup: compare the target against the root key and recurse
into the appropriate subtree. -/
DefinitionDoc Game.DataStructures.SearchTree.lookup as "SearchTree.lookup" in "Data Structures"

/-- Insert a key, leaving an existing copy unchanged. -/
DefinitionDoc Game.DataStructures.SearchTree.insert as "SearchTree.insert" in "Data Structures"

/-- In-order traversal of a search tree. -/
DefinitionDoc Game.DataStructures.SearchTree.inorder as "SearchTree.inorder" in "Data Structures"

/-- Every key stored in a tree satisfies a predicate. -/
DefinitionDoc Game.DataStructures.SearchTree.All as "SearchTree.All" in "Data Structures"

/-- The strict binary-search-tree invariant. -/
DefinitionDoc Game.DataStructures.SearchTree.IsBST as "SearchTree.IsBST" in "Data Structures"

/-- Every key bounded by a predicate over a whole tree is bounded over its
in-order traversal. -/
TheoremDoc Game.DataStructures.SearchTree.forall_mem_inorder_of_all as
  "SearchTree.forall_mem_inorder_of_all" in "Data Structures"

/-- The structural AVL balance condition. -/
DefinitionDoc Game.DataStructures.AVL.Balanced as "AVL.Balanced" in "Data Structures"

/-- Height of a search tree. -/
DefinitionDoc Game.DataStructures.AVL.height as "AVL.height" in "Data Structures"

/-- An AVL tree combines search ordering with height balance. -/
DefinitionDoc Game.DataStructures.AVL.IsAVL as "AVL.IsAVL" in "Data Structures"

/-- A chained hash table: a family of buckets indexed by hash values. -/
DefinitionDoc Game.DataStructures.HashTable as "HashTable" in "Data Structures"

/-- The empty hash table has no entries in any bucket. -/
DefinitionDoc Game.DataStructures.HashTable.empty as "HashTable.empty" in "Data Structures"

/-- Lookup checks the bucket selected by the hash function. -/
DefinitionDoc Game.DataStructures.HashTable.lookup as "HashTable.lookup" in "Data Structures"

/-- Chained insertion adds the key at the front of its bucket. -/
DefinitionDoc Game.DataStructures.HashTable.insert as "HashTable.insert" in "Data Structures"

/-- Rebuild a table from a finite key list, as during resizing or rehashing. -/
DefinitionDoc Game.DataStructures.HashTable.rebuild as "HashTable.rebuild" in "Data Structures"

/-- Rebuilding unfolds one key at a time: rebuild the tail, then insert the
head. -/
TheoremDoc Game.DataStructures.HashTable.rebuild_cons as "HashTable.rebuild_cons" in "Data Structures"

/-- After inserting `a`, a lookup for `x` succeeds exactly when `x` is the
newly inserted key or was already present. -/
TheoremDoc Game.DataStructures.HashTable.lookup_insert_iff as
  "HashTable.lookup_insert_iff" in "Data Structures"

/-- `Function.update f a v a = v`: reading back the point a function was just
updated at returns the value it was updated to. -/
TheoremDoc Function.update_self as "update_self" in "Data Structures"

/-- Parent pointers accompanied by their abstract representative map. -/
DefinitionDoc Game.DataStructures.DisjointSet as "DisjointSet" in "Data Structures"

/-- Compress one parent pointer directly to its class representative. -/
DefinitionDoc Game.DataStructures.DisjointSet.compress as "DisjointSet.compress" in
  "Data Structures"

/-- `(l.drop i).length = l.length - i`. -/
TheoremDoc List.length_drop as "length_drop" in "Prefix Strings"

/-- `(as ++ bs).length = as.length + bs.length`. -/
TheoremDoc List.length_append as "length_append" in "Prefix Strings"

/-- `(List.range n).length = n`. -/
TheoremDoc List.length_range as "length_range" in "Advanced"

/-- `(as.map f).length = as.length`. -/
TheoremDoc List.length_map as "length_map" in "Advanced"

/-- Builds a pairwise proof for `a :: l` from compatibility with every tail
element and pairwise compatibility of the tail. -/
TheoremDoc List.Pairwise.cons as "Pairwise.cons" in "Greedy Exercises"

/-- A list is a prefix of another list. -/
DefinitionDoc List.IsPrefix as "IsPrefix" in "Lists and permutations"

/-- Pairwise facts over an appended list split into each side and cross-list facts. -/
TheoremDoc List.pairwise_append as "pairwise_append" in "Sorting"

/-- Membership in a singleton list is equality with its element. -/
TheoremDoc List.mem_singleton as "mem_singleton" in "Table Dynamic Programming"

/-- Mapping a function over an appended list distributes over append. -/
TheoremDoc List.map_append as "map_append" in "Greedy Exercises"

/-- Summing an appended list splits into the sum of each side. -/
TheoremDoc List.sum_append as "sum_append" in "Greedy Exercises"

/-- Addition of natural numbers is associative. -/
TheoremDoc Nat.add_assoc as "add_assoc" in "Greedy Exercises"

/-- Addition of natural numbers is commutative. -/
TheoremDoc Nat.add_comm as "add_comm" in "Greedy Exercises"

/-- Natural-number addition can reassociate and commute the left terms. -/
TheoremDoc Nat.add_left_comm as "add_left_comm" in "Greedy Exercises"

/-- Computable predicates are closed under negation. -/
TheoremDoc ComputablePred.not as "not" in "Computability"

/-- If `c`/`f`/`g` are computable, so is `fun a => cond (c a) (f a) (g a)`
(branch on a computable Boolean). -/
TheoremDoc Computable.cond as "cond" in "Computability"

/-- A constant function is computable. -/
TheoremDoc Computable.const as "const" in "Computability"

/-- `decide (p ∧ q) = (decide p && decide q)`. -/
TheoremDoc Bool.decide_and as "decide_and" in "Computability"

/-- `decide (p ∨ q) = (decide p || decide q)`. -/
TheoremDoc Bool.decide_or as "decide_or" in "Computability"

/-- Every element is a member of the universal set: `a ∈ Set.univ`. -/
TheoremDoc Set.mem_univ as "mem_univ" in "Computability"

/-- `Code` for the always-zero program: `Code.zero`. -/
DefinitionDoc Nat.Partrec.Code.zero as "Code.zero" in "Computability"

/-- If `f` is computable and `g` agrees with `f` pointwise, `g` is
computable. -/
TheoremDoc Computable.of_eq as "of_eq" in "Computability"

/-- Computable case-splitting on a natural number's `Nat.casesOn`. -/
TheoremDoc Computable.nat_casesOn as "nat_casesOn" in "Computability"

/-- The identity function is computable. -/
TheoremDoc Computable.id as "id" in "Computability"

/-- The encoding function of a `Primcodable` type is computable. -/
TheoremDoc Computable.encode as "encode" in "Computability"

/-- `x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n`: the untimed evaluator succeeds
exactly when some step-bounded run does. -/
TheoremDoc Nat.Partrec.Code.evaln_complete as "evaln_complete" in "Computability"

/-- The step-bounded evaluator is monotone in its step budget: once it
succeeds, a larger budget succeeds with the same answer. -/
TheoremDoc Nat.Partrec.Code.evaln_mono as "evaln_mono" in "Computability"

/-- If the step-bounded evaluator succeeds, the untimed evaluator agrees
with it. -/
TheoremDoc Nat.Partrec.Code.evaln_sound as "evaln_sound" in "Computability"

/-- The witness produced by `Nat.find` satisfies the predicate it was
found for. -/
TheoremDoc Nat.find_spec as "find_spec" in "Computability"

/-- `o.isSome ↔ ∃ a, o = some a`. -/
TheoremDoc Option.isSome_iff_exists as "isSome_iff_exists" in "Computability"

/-- `a ∈ o ↔ o = some a`. -/
TheoremDoc Option.mem_def as "mem_def" in "Computability"

/-- `o.Dom ↔ ∃ y, y ∈ o`: a `Part` is defined exactly when it has a
value. -/
TheoremDoc Part.dom_iff_mem as "dom_iff_mem" in "Computability"

/-- `b ∈ s → f b ≤ s.sup f`: every element's image is at most the
finite supremum. -/
TheoremDoc Finset.le_sup as "le_sup" in "Computability"

/-- If `f`/`g` are computable, so is `fun a => (f a, g a)`. -/
TheoremDoc Computable.pair as "pair" in "Computability"

/-- `ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => f a`:
a predicate is computable iff it has a computable Boolean decider. -/
TheoremDoc ComputablePred.computable_iff as "computable_iff" in "Computability"

/-- `Option.isSome` is primitive recursive. -/
TheoremDoc Primrec.option_isSome as "option_isSome" in "Computability"

/-- `1 < b → x ≤ b ^ Nat.clog b x`: the ceiling logarithm is always a
valid exponent witness. -/
TheoremDoc Nat.le_pow_clog as "le_pow_clog" in "Natural numbers"

/-- `c ↔ dite c t e = t hc`: reduces a dependent if-then-else once its
condition is known to hold. -/
TheoremDoc dif_pos as "dif_pos" in "Logic, order, and algebra"

/-- `simp`'s reduction of a literal natural-number addition. -/
TheoremDoc Nat.reduceAdd as "reduceAdd" in "Natural numbers"

/-- `(∀ p : α × β, P p) ↔ ∀ a b, P (a, b)`: universally quantifying over
a pair is the same as quantifying over its two components. -/
TheoremDoc Prod.forall as "forall" in "Logic, order, and algebra"

/-- `p = q ↔ p.1 = q.1 ∧ p.2 = q.2`. -/
TheoremDoc Prod.ext_iff as "ext_iff" in "Logic, order, and algebra"

/-- `(a ≠ b) = ¬(a = b)`, definitionally. -/
TheoremDoc ne_eq as "ne_eq" in "Logic, order, and algebra"

/-- `a < b → a ≠ b`. -/
TheoremDoc Nat.ne_of_lt as "ne_of_lt" in "Natural numbers"

/-- `a < b → b < c → a < c`, for natural numbers. -/
TheoremDoc Nat.lt_trans as "lt_trans" in "Natural numbers"

/-- `n < n + 1`. -/
TheoremDoc Nat.lt_succ_self as "lt_succ_self" in "Natural numbers"

/-- `b ∈ l.map f ↔ ∃ a ∈ l, f a = b`. -/
TheoremDoc List.mem_map as "mem_map" in "Lists and permutations"

/-- `b ∈ bs → b ∈ as ++ bs`. -/
TheoremDoc List.mem_append_right as "mem_append_right" in "Lists and permutations"

/-- `a ∈ as → a ∈ as ++ bs`. -/
TheoremDoc List.mem_append_left as "mem_append_left" in "Lists and permutations"

/-- `(1 : α) ≠ 0`. -/
TheoremDoc one_ne_zero as "one_ne_zero" in "Complexity Classes"

/-- `(¬∃ x, p x) ↔ ∀ x, ¬ p x`. -/
TheoremDoc not_exists as "not_exists" in "Complexity Classes"

/-- `¬(a ∧ b) ↔ (a → ¬b)`. -/
TheoremDoc not_and as "not_and" in "Complexity Classes"

/-- Since only `0` and `1` are possible remainders mod `2`, `n % 2 ≠ 0`
is equivalent to `n % 2 = 1`. -/
TheoremDoc Nat.mod_two_not_eq_zero as "mod_two_not_eq_zero" in "Complexity Classes"

/-- `l.length = 0 ↔ l = []`. -/
TheoremDoc List.length_eq_zero_iff as "length_eq_zero_iff" in "Lists and permutations"

/-- `(p ↔ False) = ¬ p`. -/
TheoremDoc iff_false as "iff_false" in "Logic, order, and algebra"

/-- `(∃ a, a = a' ∧ p a) ↔ p a'`. -/
TheoremDoc exists_eq_left as "exists_eq_left" in "Logic, order, and algebra"

/-- `a ^ (m * n) = (a ^ m) ^ n`. -/
TheoremDoc pow_mul as "pow_mul" in "Complexity Classes"

/-- `n ≤ m → n ^ i ≤ m ^ i`, for natural numbers. -/
TheoremDoc Nat.pow_le_pow_left as "pow_le_pow_left" in "Natural numbers"

/-- `n ≤ m → k * n ≤ k * m`, for natural numbers. -/
TheoremDoc Nat.mul_le_mul_left as "mul_le_mul_left" in "Natural numbers"

/-- `(p ∧ p) = p`. -/
TheoremDoc and_self as "and_self" in "Logic, order, and algebra"

/-- `(p ∨ False) = p`. -/
TheoremDoc or_false as "or_false" in "Logic, order, and algebra"

/-- `(¬ True) = False`. -/
TheoremDoc not_true_eq_false as "not_true_eq_false" in "Logic, order, and algebra"

/-- `(¬ False) = True`. -/
TheoremDoc not_false_eq_true as "not_false_eq_true" in "Logic, order, and algebra"

/-- `x > y ↔ y < x`. -/
TheoremDoc gt_iff_lt as "gt_iff_lt" in "Logic, order, and algebra"

/-- `s ⊆ t ↔ ∀ x ∈ s, x ∈ t`. -/
TheoremDoc Finset.subset_iff as "subset_iff" in "Finite sets and counting"

/-- `s \ t ⊆ s`. -/
TheoremDoc Finset.sdiff_subset as "sdiff_subset" in "Finite sets and counting"

/-- `s ⊆ t → (t \ s).card = t.card - s.card`. -/
TheoremDoc Finset.card_sdiff_of_subset as "card_sdiff_of_subset" in "Finite sets and counting"

/-- `(Finset.range n).card = n`. -/
TheoremDoc Finset.card_range as "card_range" in "Finite sets and counting"

/-- `s ⊆ t → s.card ≤ t.card`. -/
TheoremDoc Finset.card_le_card as "card_le_card" in "Lower Bounds"

/-- `(False ∨ p) = p`. -/
TheoremDoc false_or as "false_or" in "Logic, order, and algebra"

/-- `¬¬a ↔ a` (classically). -/
TheoremDoc Decidable.not_not as "not_not" in "Logic and decisions"

/-- `(p ∧ True) = p`. -/
TheoremDoc and_true as "and_true" in "Logic, order, and algebra"

/-- `(a ∧ b → c) ↔ (a → b → c)`. -/
TheoremDoc and_imp as "and_imp" in "Logic, order, and algebra"

/-- `(p ∧ False) = False`. -/
TheoremDoc and_false as "and_false" in "Logic, order, and algebra"

/-- `(a * b) ^ n = a ^ n * b ^ n`. -/
TheoremDoc mul_pow as "mul_pow" in "Complexity Classes"

/-- `2 * n = n + n`. -/
TheoremDoc two_mul as "two_mul" in "Complexity Classes"

/-- `a ∈ s \ t ↔ a ∈ s ∧ a ∉ t`. -/
TheoremDoc Finset.mem_sdiff as "mem_sdiff" in "Finite sets and counting"

/-- `m ∈ Finset.range n ↔ m < n`. -/
TheoremDoc Finset.mem_range as "mem_range" in "Finite sets and counting"

/-! Theorems grouped by the levelset that first introduces them. -/

/-- (missing) -/
TheoremDoc literal_semantics as "literal_semantics" in "Advanced"

/-- (missing) -/
TheoremDoc tseitin_gates_complete as "tseitin_gates_complete" in "Advanced"

/-- (missing) -/
TheoremDoc tseitin_transform_forward as "tseitin_transform_forward" in "Advanced"

/-- (missing) -/
TheoremDoc tseitin_gate_soundness as "tseitin_gate_soundness" in "Advanced"

/-- (missing) -/
TheoremDoc tseitin_equisatisfiable as "tseitin_equisatisfiable" in "Advanced"

/-- (missing) -/
TheoremDoc tseitin_linear_size as "tseitin_linear_size" in "Advanced"

/-- (missing) -/
TheoremDoc sat_reduces_tseitin3sat as "sat_reduces_tseitin3sat" in "Advanced"

/-- (missing) -/
TheoremDoc chained_np_complete as "chained_np_complete" in "Advanced"

/-- (missing) -/
TheoremDoc hamiltonian_completeness as "hamiltonian_completeness" in "Advanced"

/-- (missing) -/
TheoremDoc deterministic_run_included as "deterministic_run_included" in "Advanced"

/-- *(lean docstring)*\
**Given** (Demo). **Potential method, telescoped form.** If each
operation has amortized cost `≤ c`, then after `n` operations the
accumulated actual cost *plus* the current potential is at most `c · n`
more than the starting potential. Demonstrated, not played; supplied
here so `potential_method_le` can cite it.  -/
TheoremDoc Game.Clockwork.potential_method as "potential_method" in "Amortized Analysis"

/-- *(lean docstring)*\
Growing a new high bit costs one unit.  -/
TheoremDoc Game.Clockwork.incCost_nil as "incCost_nil" in "Amortized Analysis"

/-- *(lean docstring)*\
`increment []` grows a new high bit: `[] ↦ [true]`.  -/
TheoremDoc Game.Clockwork.increment_nil as "increment_nil" in "Amortized Analysis"

/-- *(lean docstring)*\
**Given**: potential method, usable form — because the potential is
non-negative, the total actual cost of `n` operations is at most `c · n`
plus the initial potential. Played (re-derived) in the "Telescoping
Potential" level; supplied here so `binaryCounter_potential` can cite
it.  -/
TheoremDoc Game.Clockwork.potential_method_le as "potential_method_le" in "Amortized Analysis"

/-- *(lean docstring)*\
**Given**: the key amortized bound — the actual cost of an increment
plus the increase in the number of set bits is at most `2`, for *every*
counter state. Played (re-derived) in the "Carry Chain" level; supplied
here so `binaryCounter_potential` can cite it.  -/
TheoremDoc Game.Clockwork.increment_amortized as "increment_amortized" in "Amortized Analysis"

/-- *(lean docstring)*\
**Given** (Demo). Potential method for a sequence of operations,
telescoped form — the list-of-operations analogue of `potential_method`,
now with a data-structure invariant `Inv` the operations must preserve.
Supplied here so `potential_method_seq_le` can cite it.  -/
TheoremDoc Game.Clockwork.potential_method_seq as "potential_method_seq" in "Amortized Analysis"

/-- *(lean docstring)*\
**Given**: potential method for a sequence, usable form. Played
(re-derived) in the "Sequence Framework" level; supplied here so
`backupStack_amortized` can cite it.  -/
TheoremDoc Game.Clockwork.potential_method_seq_le as "potential_method_seq_le" in "Amortized Analysis"

/-- *(lean docstring)*\
Appending one element always increases the logical size by exactly
one, whether or not it triggers a resize.  -/
TheoremDoc Game.Clockwork.DynArray.size_append as "DynArray.size_append" in "Amortized Analysis"

/-- *(lean docstring)*\
**Given**: the banker's balance is always non-negative on well-formed
states. Needed by `dynArray_amortized`.  -/
TheoremDoc Game.Clockwork.DynArray.bal_nonneg as "DynArray.bal_nonneg" in "Amortized Analysis"

/-- (missing) -/
TheoremDoc harmonic_succ as "harmonic_succ" in "Approximation Algorithms"

/-- (missing) -/
TheoremDoc harmonic_le_one_add_log as "harmonic_le_one_add_log" in "Approximation Algorithms"

/-- *(lean docstring)*\
**Alias** of `Left.mul_pos`.

---

Assumes left covariance.  -/
TheoremDoc mul_pos as "mul_pos" in "Big-O"

/-- *(lean docstring)*\
**Given**: big-O is transitive. Played (re-derived) in the "Big-O
Calculus" level; supplied here so `IsBigTheta.trans` can cite it.  -/
TheoremDoc Game.Clockwork.IsBigO.trans as "IsBigO.trans" in "Big-O"

/-- *(lean docstring)*\
If two lists are sorted by an antisymmetric relation, and permutations of each other,
they must be equal.
 -/
TheoremDoc List.Perm.eq_of_pairwise as "List.Perm.eq_of_pairwise" in "Sorting"

/-- (missing) -/
TheoremDoc le_antisymm as "le_antisymm" in "Sorting"

/-- **Uniqueness of sorted permutations.** Two sorted lists that are permutations
of each other are equal. -/
TheoremDoc sorted_perm_unique as "sorted_perm_unique" in "Sorting"

/-- *(lean docstring)*\
**Given**: two monomial bounds combine into one — the key arithmetic
step behind closure under addition. Played (re-derived) in the
"Polynomial Time Reductions" level; supplied here so `PolyTimeSolvable.of_reducible`
and the reduction-composition proofs can cite it.  -/
TheoremDoc Game.Complexity.monomial_add_bound as "monomial_add_bound" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: feeding a polynomial bound into a monomial stays
polynomial — the key arithmetic step behind closure under composition.
Played (re-derived) in the "Polynomial Time Reductions" level; supplied here so
`PolyTimeSolvable.of_reducible` and `PolyReducible.trans` can cite it.  -/
TheoremDoc Game.Complexity.monomial_comp_bound as "monomial_comp_bound" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: a constant function is polynomially bounded. Needed by
`PolyReducible.refl`.  -/
TheoremDoc Game.Complexity.IsPolyBounded.const as "IsPolyBounded.const" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: the identity is polynomially bounded. Needed by
`PolyReducible.refl`.  -/
TheoremDoc Game.Complexity.IsPolyBounded.id as "IsPolyBounded.id" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: polynomial (indeed linear) size blow-up of the apex
reduction. Played (re-derived) in the "Three to Four Colours" level;
supplied here so `threeCol_reduces_fourCol` can cite it.  -/
TheoremDoc Game.Complexity.addApex_size as "addApex_size" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: a convenient way to build a reduction from a plain
instance map `f`, isolating the two mathematical obligations of a Karp
reduction (answer preservation and polynomial size blow-up). Needed by
every reduction-assembly level.  -/
TheoremDoc Game.Complexity.PolyReducible.of_map as "PolyReducible.of_map" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: polynomial size blow-up of the partition reduction.
Needed by `partition_reduces_subsetSum`.  -/
TheoremDoc Game.Complexity.partToSS_size as "partToSS_size" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: the fixed no-instance is genuinely a no-instance. Needed
by `indepToVC_correct`.  -/
TheoremDoc Game.Complexity.not_vertexCover_falseVCInst as "not_vertexCover_falseVCInst" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: polynomial size blow-up of the independent-set reduction.
Needed by `indepSet_reduces_vertexCover`.  -/
TheoremDoc Game.Complexity.indepToVC_size as "indepToVC_size" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: composition principle — if `A` reduces to `B` in
polynomial time and `B` is polynomial-time solvable, then `A` is
polynomial-time solvable. Needed by `inP_of_reduces`.  -/
TheoremDoc Game.Complexity.PolyTimeSolvable.of_reducible as "PolyTimeSolvable.of_reducible" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: a lazy walk witnesses reachability. Needed by
`reach_iff_reachable`.  -/
TheoremDoc Game.Complexity.lazyWalk_to_reflTransGen as "lazyWalk_to_reflTransGen" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: conversely, reachability gives a lazy walk of some length.
Needed by `reach_iff_reachable`.  -/
TheoremDoc Game.Complexity.reflTransGen_to_lazyWalk as "reflTransGen_to_lazyWalk" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: reducibility is transitive. Played (re-derived) in the
"Reduction Calculus" level; supplied here in case a later section needs
it.  -/
TheoremDoc Game.Complexity.PolyReducible.trans as "PolyReducible.trans" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: complementing both ends of a many-one reduction preserves
reducibility. Played in the "Complement Reductions" level.  -/
TheoremDoc Game.Complexity.reduceComplements as "reduceComplements" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: `P ⊆ NP` — every polynomial-time decidable problem has a
polynomial-time verifier (take the certificate type to be `Unit`, and run
the solver on the input). Played (re-derived) in the "P and NP" level;
supplied here so `P_le_NP` can cite it.  -/
TheoremDoc Game.Complexity.P_subset_NP as "P_subset_NP" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: `P` is closed under complement — negate the solver's
Boolean output, which costs one extra step and keeps the running time
polynomially bounded. Played (re-derived) in the "Complement Closure"
level; supplied here in case a later section needs it.  -/
TheoremDoc Game.Complexity.inP_compl as "inP_compl" in "Complexity Classes"

/-- *(lean docstring)*\
**Given**: Rice's theorem, index form — a behaviour-invariant set of
codes `C` is computable iff it is empty or everything. Needed by
`rice_nontrivial`.  -/
TheoremDoc Game.Complexity.rice_index as "rice_index" in "Computability"

/-- *(lean docstring)*\
A function is partial recursive if and only if there is a code implementing it. Therefore,
`eval` is a **universal partial recursive function**.  -/
TheoremDoc Nat.Partrec.Code.exists_code as "Nat.Partrec.Code.exists_code" in "Computability"

/-- *(lean docstring)*\
Invariant relationship between encoding and decoding  -/
TheoremDoc Encodable.encodek as "Encodable.encodek" in "Computability"

/-- *(lean docstring)*\
**The halting problem on blank input**, reused verbatim from Lab 21:
the set of codes that halt on input `0` is not computable. Needed by
`busy_beaver_principle`.  -/
TheoremDoc Game.Complexity.halting_on_zero_undecidable as "halting_on_zero_undecidable" in "Computability"

/-- *(lean docstring)*\
**Given**: correctness of `haltTime` — if `c` halts on input `0`,
running it for exactly `haltTime c` steps already produces an answer.
Played (re-derived) in the "Exact Halt Time" level; supplied here so
`bbSteps_not_computable` can cite it.  -/
TheoremDoc Game.Complexity.haltTime_spec as "haltTime_spec" in "Computability"

/-- (missing) -/
TheoremDoc Iff.rfl as "Iff.rfl" in "Computability"

/-- (missing) -/
TheoremDoc Computable.comp as "Computable.comp" in "Computability"

/-- (missing) -/
TheoremDoc Iff.trans as "Iff.trans" in "Computability"

/-- *(lean docstring)*\
**Given**: undecidability transports forward along a many-one
reduction. Played in the "Undecidability Transport" level; supplied here
so later levels can cite the packaged preimage argument directly.  -/
TheoremDoc Game.Complexity.undecidable_of_manyOne as "undecidable_of_manyOne" in "Computability"

/-- (missing) -/
TheoremDoc ComputablePred.to_re as "ComputablePred.to_re" in "Computability"

/-- (missing) -/
TheoremDoc ComputablePred.computable_iff_re_compl_re' as "ComputablePred.computable_iff_re_compl_re'" in "Computability"

/-- *(lean docstring)*\
**Given**: the halting set is recursively enumerable. Not needed
elsewhere, but recorded for completeness.  -/
TheoremDoc Game.Complexity.halting_re as "halting_re" in "Computability"

/-- *(lean docstring)*\
**Given**: the halting set's complement is not r.e. Not needed
elsewhere, but recorded for completeness.  -/
TheoremDoc Game.Complexity.halting_compl_not_re as "halting_compl_not_re" in "Computability"

/-- *(lean docstring)*\
**Given**: a behaviour-invariant, nontrivial property of program
codes is undecidable. This packages `rice_index` into the form used by
the Totality/Emptiness/Equivalence levels.  -/
TheoremDoc Game.Complexity.rice_nontrivial as "rice_nontrivial" in "Computability"

/-- *(lean docstring)*\
**Given**: a constant program halts on every input. Used as a
yes-witness for `Total`.  -/
TheoremDoc Game.Complexity.const_total as "const_total" in "Computability"

/-- *(lean docstring)*\
**Given**: the constant-zero program is not empty. Used as a
counterexample for `Empty`.  -/
TheoremDoc Game.Complexity.const_zero_not_empty as "const_zero_not_empty" in "Computability"

/-- *(lean docstring)*\
**Given**: the constant-zero and constant-one programs are not
extensionally equivalent. Used to obtain a no-witness for
`EquivalentTo base`.  -/
TheoremDoc Game.Complexity.const_zero_ne_const_one as "const_zero_ne_const_one" in "Computability"

/-- *(lean docstring)*\
**Given**: achievability — there is a feasible selection attaining the
DP value. Given whole for the "Knapsack Optimality" boss level to
assemble.  -/
TheoremDoc Game.Design.knap_achievable as "knap_achievable" in "Dynamic Programming"

/-- *(lean docstring)*\
**Given**: optimality upper bound — every feasible selection obtains
value at most the DP value. Out of scope for "Knapsack Recurrence" (which
plays only `knap_tail_le`); given whole for the "Knapsack Optimality" boss
level to assemble.  -/
TheoremDoc Game.Design.knap_upper_bound as "knap_upper_bound" in "Dynamic Programming"

/-- *(lean docstring)*\
**Given**: the DP recurrence solves the 0/1 knapsack — the assembled
achievability/optimality contract. Played (re-assembled) in the "Knapsack
Optimality" boss level; supplied here so "Certified Knapsack" can transfer
it to the proof-carrying implementation.  -/
TheoremDoc Game.Design.knap_is_optimal as "knap_is_optimal" in "Dynamic Programming"

/-- *(lean docstring)*\
**Given**: with positive denominations, the DP value is `⊤` exactly when
there is no way to make change.  -/
TheoremDoc Game.Design.minCoins_top_iff_no_rep as "minCoins_top_iff_no_rep" in "Dynamic Programming"

/-- *(lean docstring)*\
**Given**: if the DP value is finite, some representation uses exactly
that many coins.  -/
TheoremDoc Game.Design.minCoins_achievable as "minCoins_achievable" in "Dynamic Programming"

/-- *(lean docstring)*\
**Given**: the DP recurrence solves coin change — the assembled
least-coins contract. Played (re-assembled) in the "Coin Optimality" level;
supplied here so "Certified Change" can transfer it to the proof-carrying
implementation.  -/
TheoremDoc Game.Design.minCoins_isLeast as "minCoins_isLeast" in "Dynamic Programming"

/-- *(lean docstring)*\
See `le_div_iff₀'` for a version with multiplication on the other side.  -/
TheoremDoc le_div_iff₀ as "le_div_iff₀" in "Greedy"

/-- *(lean docstring)*\
**Given**: the greedy choice is feasible.  -/
TheoremDoc Game.Design.greedyAssign_feasible as "greedyAssign_feasible" in "Greedy"

/-- *(lean docstring)*\
**Given**: the greedy choice obtains exactly the greedy value.  -/
TheoremDoc Game.Design.greedyAssign_value as "greedyAssign_value" in "Greedy"

/-- *(lean docstring)*\
The relation `≤` on a preorder is transitive.  -/
TheoremDoc le_trans as "le_trans" in "Greedy Exercises"

/-- *(lean docstring)*\
**Given**: from `SortedByDensity`, every material's density is bounded by
the head's density `it.v / it.w`. Played (re-derived) in the "Exchange
Density order" level; supplied here so `greedy_upper_bound` can cite it.  -/
TheoremDoc Game.Design.density_bound_of_sorted as "density_bound_of_sorted" in "Greedy Exercises"

/-- *(lean docstring)*\
Unfolds `IsHeap` at a `node`: the root dominates both subtrees, and
both subtrees are themselves heaps.  -/
TheoremDoc Game.Clockwork.isHeap_node_iff as "isHeap_node_iff" in "Sorting"

/-- *(lean docstring)*\
**Given**: `merge` keeps every element — its output is a permutation
of the two inputs concatenated. Not played as a separate level (its
`Sorry`-free proof needs strong induction on the combined size), but
supplied since `merge_isHeap`, `buildHeap`'s and `popAll`'s facts all rely
on it.  -/
TheoremDoc Game.Clockwork.elems_merge as "elems_merge" in "Sorting"

/-- *(lean docstring)*\
**Given**: insertion maintains the heap invariant. Needed by
`buildHeap_isHeap`.  -/
TheoremDoc Game.Clockwork.insert_isHeap as "insert_isHeap" in "Sorting"

/-- *(lean docstring)*\
**Given**: insertion adds exactly the new key. Needed by
`elems_buildHeap`.  -/
TheoremDoc Game.Clockwork.elems_insert as "elems_insert" in "Sorting"

/-- *(lean docstring)*\
**Given**: popping a heap yields a decreasing list. Played
(re-derived) in the "Heap Sort Correctness" level; supplied here so
`heapSort_sorted` can cite it.  -/
TheoremDoc Game.Clockwork.popAll_sorted as "popAll_sorted" in "Sorting"

/-- *(lean docstring)*\
**Given**: building a heap maintains the invariant at every step.
Played (re-derived) in the "Heap Construction" level; supplied here so
`popAllFuel_sorted` can cite it.  -/
TheoremDoc Game.Clockwork.buildHeap_isHeap as "buildHeap_isHeap" in "Sorting"

/-- *(lean docstring)*\
If two lists are identical except for having their first two elements swapped, then they are
permutations of each other: `x::y::l ~ y::x::l`.
 -/
TheoremDoc List.Perm.swap as "List.Perm.swap" in "Sorting"

/-- *(lean docstring)*\
**Given**: `bubbleSort` returns a sorted list — the other half of the
"Bubble Sort Correctness" level's assembled contract.  -/
TheoremDoc Game.Contracts.bubbleSort_sorted as "bubbleSort_sorted" in "Sorting"

/-- *(lean docstring)*\
**Given**: `bubbleSort` returns a permutation of its input — one half of
the "Bubble Sort Correctness" level's assembled contract.  -/
TheoremDoc Game.Contracts.bubbleSort_perm as "bubbleSort_perm" in "Sorting"

/-- *(lean docstring)*\
**Given**: `selectionSort` returns a sorted list — the other half of the
"Selection Sort Correctness" level's assembled contract.  -/
TheoremDoc Game.Contracts.selectionSort_sorted as "selectionSort_sorted" in "Sorting"

/-- *(lean docstring)*\
**Given**: `selectionSort` returns a permutation of its input — one half
of the "Selection Sort Correctness" level's assembled contract.  -/
TheoremDoc Game.Contracts.selectionSort_perm as "selectionSort_perm" in "Sorting"

/-- *(lean docstring)*\
The result of `mergeSort` is sorted,
as long as the comparison function is transitive (`le a b → le b c → le a c`)
and total in the sense that `le a b || le b a`.

The comparison function need not be irreflexive, i.e. `le a b` and `le b a` is allowed even when `a ≠ b`.
 -/
TheoremDoc List.pairwise_mergeSort as "List.pairwise_mergeSort" in "Sorting"

/-- *(lean docstring)*\
Supplied "card": on a sorted array, searching the window `[lo, hi)` succeeds
iff `target` occurs at some index inside that window. This is the interval
invariant the `BinarySearch` boss level is allowed to use as a black box.  -/
TheoremDoc Game.Contracts.binarySearchAux_spec as "binarySearchAux_spec" in "Hoare triples"

/-- *(lean docstring)*\
The relation `≤` on a preorder is reflexive.  -/
TheoremDoc le_refl as "le_refl" in "Hoare triples"

/-- *(lean docstring)*\
If one list is a permutation of the other, adding the same element as the head of each yields
lists that are permutations of each other: `l₁ ~ l₂ → x::l₁ ~ x::l₂`.
 -/
TheoremDoc List.Perm.cons as "List.Perm.cons" in "Sorting"

/-- Inserting one element only rearranges the resulting list. -/
TheoremDoc insert_perm as "insert_perm" in "Sorting"

/-- A common lower bound is preserved by insertion. -/
TheoremDoc insert_lower_bound as "insert_lower_bound" in "Sorting"

/-- Base case of the sortedness invariant: `insert x []` is sorted. -/
TheoremDoc insert_sorted_nil as "insert_sorted_nil" in "Sorting"

/-- Sortedness step, first branch (`x ≤ y`): the new element becomes the head. -/
TheoremDoc insert_sorted_head as "insert_sorted_head" in "Sorting"

/-- Sortedness step, second branch (`¬ x ≤ y`): the old head is kept. -/
TheoremDoc insert_sorted_tail as "insert_sorted_tail" in "Sorting"

/-- Inductive step of the sortedness invariant. -/
TheoremDoc insert_sorted_cons as "insert_sorted_cons" in "Sorting"

/-- Insertion into a sorted list remains sorted. -/
TheoremDoc insert_sorted as "insert_sorted" in "Sorting"

/-- Full functional correctness for inserting one element. -/
TheoremDoc insert_correct as "insert_correct" in "Sorting"

/-- Insertion sort preserves all input elements and their multiplicities. -/
TheoremDoc insertionSort_perm as "insertionSort_perm" in "Sorting"

/-- *(lean docstring)*\
All elements of the empty list are vacuously pairwise related.  -/
TheoremDoc List.Pairwise.nil as "List.Pairwise.nil" in "Sorting"

/-- The output of insertion sort is sorted. -/
TheoremDoc insertionSort_sorted as "insertionSort_sorted" in "Sorting"

/-- Full functional correctness of insertion sort. -/
TheoremDoc insertionSort_correct as "insertionSort_correct" in "Sorting"

/-- Insertion increases the length of the list by exactly one. -/
TheoremDoc insert_length as "insert_length" in "Sorting"

/-- Insertion sort preserves the length of its input. -/
TheoremDoc insertionSort_length as "insertionSort_length" in "Sorting"

/-- An element belongs to the sorted list exactly when it belongs to the input. -/
TheoremDoc insertionSort_mem as "insertionSort_mem" in "Sorting"

/-- Inserting one element costs at most as many comparisons as the list is long. -/
TheoremDoc insertCost_le_length as "insertCost_le_length" in "Sorting"

/-- Inserting into a sorted tail costs at most the original tail's length. -/
TheoremDoc insertCost_insertionSort_le as "insertCost_insertionSort_le" in "Sorting"

/-- Insertion sort performs at most a quadratic number of comparisons. -/
TheoremDoc insertionSortCost_le as "insertionSortCost_le" in "Sorting"

/-- *(lean docstring)*\
A polynomial-time algorithm for an NP-hard problem collapses `P` and
`NP`.  -/
TheoremDoc Game.LowerBounds.p_eq_np_of_hard_in_p as "p_eq_np_of_hard_in_p" in "Lower Bounds"

/-- *(lean docstring)*\
**Given**: merge sort returns a sorted list. Needed by
`sortsAgree`.  -/
TheoremDoc Game.Clockwork.mergeSortT_sorted as "mergeSortT_sorted" in "Sorting"

/-- *(lean docstring)*\
**Given**: merge sort only rearranges elements. Needed by
`sortsAgree`.  -/
TheoremDoc Game.Clockwork.mergeSortT_perm as "mergeSortT_perm" in "Sorting"

/-- *(lean docstring)*\
**Given**: the defining recurrence of `mstime`, valid for `n ≥ 2`.
Needed by `mstime_pow`, `mstime_le`, `mstime_ge`.  -/
TheoremDoc Game.Clockwork.mstime_rec as "mstime_rec" in "Sorting"

/-- *(lean docstring)*\
**Given**: upper bound `mstime n ≤ n · ⌈log₂ n⌉`. Needed by
`mstime_isBigTheta_nlogn`.  -/
TheoremDoc Game.Clockwork.mstime_le as "mstime_le" in "Sorting"

/-- (missing) -/
TheoremDoc Nat.even_or_odd' as "Nat.even_or_odd'" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.add_div as "Nat.add_div" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc binaryPowAux_invariant as "binaryPowAux_invariant" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.gcd_comm as "Nat.gcd_comm" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.gcd_rec as "Nat.gcd_rec" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.mod_lt as "Nat.mod_lt" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.pos_of_ne_zero as "Nat.pos_of_ne_zero" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc lt_of_le_of_lt as "lt_of_le_of_lt" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.mul_mod as "Nat.mul_mod" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.pow_succ' as "Nat.pow_succ'" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.pow_mul as "Nat.pow_mul" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.pow_mod as "Nat.pow_mod" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc modularPowAux_invariant as "modularPowAux_invariant" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.lt_succ_iff as "Nat.lt_succ_iff" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc Nat.prime_def_lt' as "Nat.prime_def_lt'" in "Numeric Algorithms"

/-- (missing) -/
TheoremDoc List.filter_append_perm as "List.filter_append_perm" in "Sorting"

/-- A single bit pass is a permutation of its input. -/
TheoremDoc bitPass_perm as "bitPass_perm" in "Sorting"

/-- *(lean docstring)*\
Permutation is transitive: `l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃`.
 -/
TheoremDoc List.Perm.trans as "List.Perm.trans" in "Sorting"

/-- Radix sort is a permutation of its input. -/
TheoremDoc radixSort_perm as "radixSort_perm" in "Sorting"

/-- (missing) -/
TheoremDoc List.Pairwise.filter as "List.Pairwise.filter" in "Sorting"

/-- One bit pass turns a list sorted by its low `i` bits into one sorted by its
low `i + 1` bits. -/
TheoremDoc bitPass_pairwise_step as "bitPass_pairwise_step" in "Sorting"

/-- (missing) -/
TheoremDoc List.pairwise_of_forall_sublist as "List.pairwise_of_forall_sublist" in "Sorting"

/-- (missing) -/
TheoremDoc Nat.mod_one as "Nat.mod_one" in "Sorting"

/-- After `n` passes, radix sort is sorted by the low `n` bits of each element. -/
TheoremDoc radixSort_pairwise_key as "radixSort_pairwise_key" in "Sorting"

/-- Radix sort with `n` passes fully sorts any list whose elements are all below
`2 ^ n`. -/
TheoremDoc radixSort_sorted as "radixSort_sorted" in "Sorting"

/-- Full functional correctness of radix sort. -/
TheoremDoc radixSort_correct as "radixSort_correct" in "Sorting"

/-- (missing) -/
TheoremDoc List.filter_append as "List.filter_append" in "Randomized Algorithms"

/-- (missing) -/
TheoremDoc List.sum_replicate as "List.sum_replicate" in "Randomized Algorithms"

/-- (missing) -/
TheoremDoc List.length_pos_iff as "List.length_pos_iff" in "Randomized Algorithms"

/-- *(lean docstring)*\
**Alias** of `left_distrib`. -/
TheoremDoc mul_add as "mul_add" in "Recurrence"

/-- *(lean docstring)*\
**Given**: closed form of the recurrence. Played (re-derived) in the
"Recurrence Unrolling" level; supplied here so `masterSeq_case1`/
`masterSeq_case2` can cite it.  -/
TheoremDoc Game.Clockwork.masterSeq_closed as "masterSeq_closed" in "Recurrence"

/-- *(lean docstring)*\
**Given**: the nonrecursive work in Case 1 contributes only a constant
multiple of `aᵏ`. Needed by `masterSeq_case1`.  -/
TheoremDoc Game.Clockwork.masterSeq_case1_sum_upper as "masterSeq_case1_sum_upper" in "Recurrence"

/-- *(lean docstring)*\
See `zero_lt_two'` for a version with the type explicit.  -/
TheoremDoc zero_lt_two as "zero_lt_two" in "Recurrence"

/-- `select` neither loses nor duplicates elements. -/
TheoremDoc select_perm as "select_perm" in "Sorting"

/-- The minimum `select` extracts is `≤` the starting candidate. -/
TheoremDoc select_le as "select_le" in "Sorting"

/-- The element `select` extracts is `≤` every leftover element. -/
TheoremDoc select_min as "select_min" in "Sorting"

/-- Selection sort preserves all input elements and their multiplicities. -/
TheoremDoc selectionSort_perm as "selectionSort_perm" in "Sorting"

/-- The output of selection sort is sorted. -/
TheoremDoc selectionSort_sorted as "selectionSort_sorted" in "Sorting"

/-- Full functional correctness of selection sort. -/
TheoremDoc selectionSort_correct as "selectionSort_correct" in "Sorting"

/-- *(lean docstring)*\
**Given**: boundary value — an empty first list has no common
subsequence. Needed by `lcs_sublist_left`/`lcs_sublist_right` and
`lcs_length_max`.  -/
TheoremDoc Game.Design.lcs_nil_left as "lcs_nil_left" in "Sequences"

/-- *(lean docstring)*\
**Given**: boundary value — an empty second list has no common
subsequence.  -/
TheoremDoc Game.Design.lcs_nil_right as "lcs_nil_right" in "Sequences"

/-- *(lean docstring)*\
**Given**: `lcs xs ys` is a subsequence of its first argument. Played
(re-derived) in the "LCS Feasibility" level; supplied here so `lcs_spec`
can cite it.  -/
TheoremDoc Game.Design.lcs_sublist_left as "lcs_sublist_left" in "Sequences"

/-- *(lean docstring)*\
**Given**: `lcs xs ys` is a subsequence of its second argument. Played
(re-derived) in the "LCS Feasibility" level; supplied here so `lcs_spec`
can cite it.  -/
TheoremDoc Game.Design.lcs_sublist_right as "lcs_sublist_right" in "Sequences"

/-- *(lean docstring)*\
**Given**: achievability — some tree shape on `len` keys attains the DP
value. Given whole for "Optimal Tree" to assemble.  -/
TheoremDoc Game.Design.exists_tcost_eq_optCost as "exists_tcost_eq_optCost" in "Sequences"

/-- *(lean docstring)*\
**Given**: lower bound — no tree shape on `len` keys costs less than
the DP value. Out of scope for "Root Candidates" (which plays only
`minRoots_le`/`minRoots_exists`); given whole for "Optimal Tree" to
assemble.  -/
TheoremDoc Game.Design.optCost_le_tcost as "optCost_le_tcost" in "Sequences"

/-- *(lean docstring)*\
**Given**: optimality of the DP — the assembled least-cost contract.
Played (re-assembled) in the "Optimal Tree" boss level; supplied here so
"Certified Tree" can transfer it to the proof-carrying implementation.  -/
TheoremDoc Game.Design.optCost_isLeast as "optCost_isLeast" in "Sequences"

/-- *(lean docstring)*\
**Alias** of `congrArg`. -/
TheoremDoc congr_arg as "congr_arg" in "Sequences"

/-- *(lean docstring)*\
The second element of a pair.  -/
TheoremDoc Prod.snd as "Prod.snd" in "Sequences"

/-- *(lean docstring)*\
**Given**: `maxSubSum l` is attained by some contiguous block
`(l.take j).drop i`. Out of scope for "Max Prefix Sum Upper Bound" (bonus there);
given whole since `kadane_isGreatest` needs it.  -/
TheoremDoc Game.Design.maxSubSum_mem as "maxSubSum_mem" in "Sequences"

/-- *(lean docstring)*\
**Given**: `maxSubSum l` upper-bounds the sum of every contiguous block
`(l.take j).drop i`. Needed by `kadane_isGreatest`.  -/
TheoremDoc Game.Design.maxSubSum_ub as "maxSubSum_ub" in "Sequences"

/-- *(lean docstring)*\
**Given**: reading off the invariant — `kadane` computes `maxSubSum`.  -/
TheoremDoc Game.Design.kadane_eq as "kadane_eq" in "Sequences"

/-- **Any two sorting functions agree.** If `f` and `g` both satisfy `IsSort`,
then `f s = g s` for every input `s`. -/
TheoremDoc isSort_eq as "isSort_eq" in "Sorting"

/-- Insertion sort satisfies the shared sorting contract. -/
TheoremDoc insertionSort_isSort as "insertionSort_isSort" in "Sorting"

/-- Selection sort satisfies the shared sorting contract. -/
TheoremDoc selectionSort_isSort as "selectionSort_isSort" in "Sorting"

/-- *(lean docstring)*\
**Given**: the number of distinct outputs is at most the number of
leaves. Needed by `factorial_le_numLeaves`.  -/
TheoremDoc Game.Clockwork.outputs_card_le_numLeaves as "outputs_card_le_numLeaves" in "Sorting"

/-- *(lean docstring)*\
**Given**: every run ends at one of the tree's leaves, so its output is
one of the recorded outputs. Needed by `factorial_le_numLeaves`.  -/
TheoremDoc Game.Clockwork.run_mem_outputs as "run_mem_outputs" in "Sorting"

/-- *(lean docstring)*\
**Given**: taking logarithms, `n · log n ≤ 2 · log (n!)`. Needed by
`comparison_sort_lower_bound`.  -/
TheoremDoc Game.Clockwork.mul_log_le_two_mul_log_factorial as "mul_log_le_two_mul_log_factorial" in "Sorting"

/-- *(lean docstring)*\
**Given**: `nil` is a right identity for `append`. Played in the "List
Append Identity" level; supplied here so later levels can cite it directly.  -/
TheoremDoc Game.Induction.List.append_nil as "List.append_nil" in "Structural induction"

/-- *(lean docstring)*\
**Given**: append is associative. Played in the "List Append
Associative" level; supplied here so "List Reverse Append" can cite it
directly.  -/
TheoremDoc Game.Induction.List.append_assoc as "List.append_assoc" in "Structural induction"

/-- *(lean docstring)*\
**Given**: reversing an append reverses the order of the parts. Played
in the "List Reverse Append" level; supplied here so "Reverse Is Involutive"
can cite it directly.  -/
TheoremDoc Game.Induction.List.rev_append as "List.rev_append" in "Structural induction"

/-- *(lean docstring)*\
**Given**: length distributes over append. Played in the "List Append Length"
level; supplied here so "Tree Inorder Length" can cite it directly.  -/
TheoremDoc Game.Induction.List.len_append as "List.len_append" in "Structural induction"

/-- *(lean docstring)*\
**Given**: mirroring twice gives back the original tree. Played in the
"Tree Mirror Involutive" level; supplied here so later levels can cite it
directly.  -/
TheoremDoc Game.Induction.Tree.mirror_mirror as "Tree.mirror_mirror" in "Structural induction"

/-- *(lean docstring)*\
**Given**: mirroring preserves the number of nodes. Played in the
"Tree Mirror Preserves Size" level; supplied here so later levels can cite it
directly.  -/
TheoremDoc Game.Induction.Tree.size_mirror as "Tree.size_mirror" in "Structural induction"

/-- *(lean docstring)*\
If `l₁` is a subsequence of `l₂`, then `a :: l₁` is a subsequence of `a :: l₂`.  -/
TheoremDoc List.Sublist.cons₂ as "List.Sublist.cons₂" in "Table Dynamic Programming"
