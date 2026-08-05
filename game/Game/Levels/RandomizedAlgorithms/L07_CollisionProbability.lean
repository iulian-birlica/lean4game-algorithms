import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 7
Title "Collision Probability Bound"
-- source: ../game/Game/Worlds/W10Randomized/L07CollisionProbability.lean

Introduction "The cross-multiplied universal-hashing count can be rewritten as
the familiar collision-probability upper bound `1 / buckets`."

Statement (κ : Type) (buckets : Nat) (family : List (κ → Fin buckets)) :
    UniversalHashFamily family → ∀ x y : κ,
      family ≠ [] → 0 < buckets → x ≠ y →
      probability family (fun hash => hash x == hash y) ≤ (1 : ℚ) / buckets := by
  Hint "Unfold `probability`, remove the empty-family branch using
  `family ≠ []`, and clear denominators with `div_le_div_iff₀`."
  intro h_family x y h_nonempty h_buckets hxy
  rw [probability]
  rw [if_neg (by simpa using h_nonempty), div_le_div_iff₀] <;> norm_cast
  · simpa [mul_comm] using h_family x y hxy
  · exact List.length_pos_iff.mpr h_nonempty

Conclusion "Universal hashing now yields the standard collision-probability bound."

NewTactic intro rw norm_num
NewTheorem List.length_pos_iff
