import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 9
Title "Savitch's Theorem"
-- source: RequestProject Lab20.reach_iff_reachable, Lab20.savitch_reachability

Introduction "**Savitch's crux.** If `2^k` is at least the number of configurations, `reach
step k` decides reachability *exactly* — any reachable pair is connected by a walk visiting at
most `Fintype.card V ≤ 2^k` configurations (the supplied pigeonhole-shrinking fact). Prove this,
then specialise to the recursion depth `k = ⌈log₂ N⌉` for the packaged Savitch statement: the
halving recursion decides reachability in `O(log² N)` working space."

Statement {V : Type*} [Fintype V] (step : V → V → Prop) :
    (∀ (k : ℕ), Fintype.card V ≤ 2 ^ k → ∀ (u v : V),
      reach step k u v ↔ Relation.ReflTransGen step u v) ∧
    (∀ (u v : V), reach step (Nat.clog 2 (Fintype.card V)) u v ↔ Relation.ReflTransGen step u v) := by
  Hint "Forward: a bounded walk always witnesses reachability. Backward: reachability gives
  *some* walk (supplied `reflTransGen_to_lazyWalk`), which pigeonhole-shrinks (supplied
  `lazyWalk_card`) to length `Fintype.card V ≤ 2^k`, hence to length exactly `2^k` by
  `lazyWalk_mono_le`."
  have hreach : ∀ (k : ℕ), Fintype.card V ≤ 2 ^ k → ∀ (u v : V),
      reach step k u v ↔ Relation.ReflTransGen step u v := by
    intro k h u v
    constructor
    · intro h_walk
      apply lazyWalk_to_reflTransGen
      exact h_walk
    · intro h
      have h_card : LazyWalk step (Fintype.card V) u v := by
        obtain ⟨w, hw⟩ := reflTransGen_to_lazyWalk _ h
        exact lazyWalk_card _ hw
      exact lazyWalk_mono_le _ (by linarith) h_card
  Hint (hidden := true) "The packaged statement is `hreach` specialised at `k := Nat.clog 2
  (Fintype.card V)`, using the supplied `Nat.le_pow_clog` to discharge the size hypothesis."
  exact ⟨hreach, fun u v => hreach _ (Nat.le_pow_clog (by norm_num) _) u v⟩

Conclusion "Verified: the halving recursion `reach` decides reachability exactly, in
`O(log² N)` working space — the deterministic simulation behind `NSPACE(f) ⊆ DSPACE(f²)`."

NewDefinition Relation.ReflTransGen Fintype.card
NewTheorem Game.Complexity.lazyWalk_to_reflTransGen Game.Complexity.reflTransGen_to_lazyWalk
  Game.Complexity.lazyWalk_card Game.Complexity.lazyWalk_mono_le Nat.le_pow_clog
