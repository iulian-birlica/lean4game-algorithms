import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 4
Title "Optimal Root Minimum"
-- source: RequestProject Lab08.minRoots_le, Lab08.minRoots_exists

Introduction "Optimal BST is an *interval* DP: the best cost for a key
range is a minimum over every candidate root. `minRoots f n = min (f 0) …
(f n)`. Prove it is both a genuine lower bound and actually attained."

Statement (f : ℕ → ℕ) (n : ℕ) :
    (∀ r ≤ n, minRoots f n ≤ f r) ∧ (∃ r ≤ n, minRoots f n = f r) := by
  Hint "Prove the two facts separately, each by induction on `n`."
  constructor
  · induction' n with n ih
    · intro r hr; rw [Nat.le_zero.mp hr]; simp only [minRoots, le_refl]
    · intro r hr
      Hint (hidden := true) "Case on `hr : r ≤ n + 1`; `simp [minRoots]` handles both."
      cases hr <;> simp_all +decide [minRoots]
  · induction' n with n ih
    · exact ⟨0, by norm_num, rfl⟩
    · obtain ⟨r0, hr0, hr0eq⟩ := ih
      rw [minRoots]
      Hint (hidden := true) "Case on whether the new root `n+1` or the previous best `r0`
      wins the minimum."
      rcases le_total (f (n + 1)) (minRoots f n) with hle | hle
      · exact ⟨n + 1, Nat.le_refl _, min_eq_left hle⟩
      · exact ⟨r0, Nat.le_succ_of_le hr0, by rw [min_eq_right hle]; exact hr0eq⟩

Conclusion "Verified: the best root over a range is a genuine, attained minimum."

NewDefinition Game.Design.minRoots
NewTheorem Nat.le_zero min_eq_left min_eq_right le_total Nat.le_succ_of_le Nat.le_refl
