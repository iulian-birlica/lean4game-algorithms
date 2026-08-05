import Game.Metadata
import Game.Support.Design

open Game.Design

World "Strings"
Level 3
Title "Rabin-Karp Correctness"
-- source: RequestProject Lab10.rkMatches_eq_naiveMatches, Lab10.mem_rkMatches

Introduction "**Equivalence of the two matchers.** Rabin–Karp verifies
every fingerprint hit with a real comparison, so it never reports a
spurious match — for *every* hash base `B`, it returns exactly what the
naive matcher returns. Prove the equivalence, then read off Rabin–Karp's
own specification for free."

Statement (B : ℕ) (text pat : List ℕ) (i : ℕ) :
    rkMatches B text pat = naiveMatches text pat ∧
      (i ∈ rkMatches B text pat ↔ i ≤ text.length ∧ matchAt text pat i) := by
  Hint "Prove the equivalence first, then read off Rabin-Karp's own
  specification through it."
  have heq : rkMatches B text pat = naiveMatches text pat := by
    Hint (hidden := true) "`List.filter_congr` reduces this to: the two decision
    procedures agree at every candidate index. Case on whether the window truly
    matches."
    refine' List.filter_congr fun i hi => _
    by_cases hb : (text.drop i).take pat.length = pat
    · rw [decide_eq_true hb, Bool.and_true, decide_eq_true (hashList_eq_of_eq B hb)]
    · rw [decide_eq_false hb, Bool.and_false]
  refine ⟨heq, ?_⟩
  Hint (hidden := true) "`rw [heq]; exact mem_naiveMatches text pat i`."
  rw [heq]
  exact mem_naiveMatches text pat i

Conclusion "Verified: Rabin-Karp agrees with the naive matcher, always."

NewDefinition Game.Design.rkMatches
NewTheorem List.filter_congr decide_eq_true decide_eq_false Bool.and_true Bool.and_false
  Game.Design.hashList_eq_of_eq Game.Design.mem_naiveMatches
