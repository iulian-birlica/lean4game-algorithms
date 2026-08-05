import Game.Metadata
import Game.Support.Contracts

World "HoareTripleExercises"
Level 7
Title "Digital Root Correctness"
-- source: RequestProject Lab04.control_le9, Lab04.control_modEq, Lab04.control_eq

Introduction "`control` iterates `digitSum` until a single digit remains —
the digital root. Prove it stays in range, that summing digits preserves
the value modulo 9, and — assembling both — its exact closed form."

Statement (n : ℕ) :
    Game.Contracts.control n ≤ 9 ∧ Game.Contracts.control n ≡ n [MOD 9] ∧
      Game.Contracts.control n = if n = 0 then 0 else (n - 1) % 9 + 1 := by
  Hint "Establish the range bound and the mod-9 invariant as general facts first
  (each its own induction via `control.induct`), then assemble the closed form."
  have hle : ∀ n, Game.Contracts.control n ≤ 9 := by
    intro n
    induction n using Game.Contracts.control.induct with
    | case1 n hn ih => rw [Game.Contracts.control, if_pos hn]; exact ih
    | case2 n hn => rw [Game.Contracts.control, if_neg hn]; omega
  have hmod : ∀ n, Game.Contracts.control n ≡ n [MOD 9] := by
    intro n
    induction n using Game.Contracts.control.induct with
    | case1 n hn ih =>
      rw [Game.Contracts.control, if_pos hn]
      have hd : Game.Contracts.digitSum n ≡ n [MOD 9] :=
        (Nat.modEq_digits_sum 9 10 (by norm_num) n).symm
      exact ih.trans hd
    | case2 n hn => rw [Game.Contracts.control, if_neg hn]
  refine ⟨hle n, hmod n, ?_⟩
  Hint (hidden := true) "Case on `n = 0` vs `n = n' + 1`; the successor case combines
  `control_pos`, the range bound, and the mod-9 fact with `omega`."
  rcases n with _ | n
  · rw [Game.Contracts.control, if_neg (by norm_num), if_pos rfl]
  · rw [if_neg (Nat.succ_ne_zero n)]
    have hb : 1 ≤ Game.Contracts.control (n + 1) ∧ Game.Contracts.control (n + 1) ≤ 9 :=
      ⟨Game.Contracts.control_pos _ (Nat.succ_pos _), hle _⟩
    have hmod2 : Game.Contracts.control (n + 1) % 9 = (n + 1) % 9 := hmod (n + 1)
    omega

Conclusion "Verified: `control` computes the digital root, exactly."

NewDefinition Game.Contracts.control Game.Contracts.digitSum Game.Contracts.control.induct
NewTheorem Nat.modEq_digits_sum Nat.ModEq.trans Nat.succ_ne_zero
  Game.Contracts.control_pos
