import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 8
Title "Savitch Reachability"
-- source: RequestProject Lab20.lazyWalk_add, Lab20.reach_succ

Introduction "**Savitch's theorem**, at its mathematical core, is a space-efficient
reachability algorithm on a configuration graph. Model 'reachable within `n` steps' as a
**lazy walk**: a sequence that at each step either stays put or follows `step`. Prove a walk of
length `n + m` splits at a midpoint into a walk of length `n` then one of length `m` — the
combinatorial heart of the halving recursion — then derive the halving recursion itself for
`reach` (reachable within `2^k` steps)."

Statement {V : Type*} (step : V → V → Prop) :
    (∀ {n m : ℕ} {u v : V},
      LazyWalk step (n + m) u v ↔ ∃ w, LazyWalk step n u w ∧ LazyWalk step m w v) ∧
    (∀ (k : ℕ) (u v : V),
      reach step (k + 1) u v ↔ ∃ w, reach step k u w ∧ reach step k w v) := by
  Hint "Splitting: from a walk of length `n + m`, the midpoint is the value at index `n`; clip the
  walk to `[0, n]` for the first half and shift the walk by `n` for the second. Joining: splice the
  two walks at index `n`."
  have hadd : ∀ {n m : ℕ} {u v : V},
      LazyWalk step (n + m) u v ↔ ∃ w, LazyWalk step n u w ∧ LazyWalk step m w v := by
    intro n m u v
    constructor
    · rintro ⟨f, hf⟩
      refine' ⟨f n, ⟨fun i => f (Min.min i n), _, _, _⟩, ⟨fun i => f (n + i), _, _, _⟩⟩ <;>
        simp_all +decide; all_goals grind
    · rintro ⟨w, hw₁, hw₂⟩
      obtain ⟨f, hf₁, hf₂, hf₃⟩ := hw₁
      obtain ⟨g, hg₁, hg₂, hg₃⟩ := hw₂
      use fun i => if i ≤ n then f i else g (i - n)
      grind
  refine ⟨hadd, ?_⟩
  Hint (hidden := true) "Unfold `reach` on both sides, rewrite `2^(k+1)` as `2^k + 2^k` via
  `pow_succ'`/`two_mul`, then apply the splitting fact `hadd` you just proved."
  intro k u v
  rw [reach]
  rw [pow_succ', two_mul, hadd]
  rfl

Conclusion "Verified: lazy walks split at any midpoint, and `reach`'s halving recursion follows
directly."

NewDefinition Game.Complexity.LazyWalk Game.Complexity.reach Min.min
NewTactic all_goals
NewTheorem two_mul
