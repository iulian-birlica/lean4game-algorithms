import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 6
Title "Universal Hashing Counts"
-- source: ../game/Game/Worlds/W10Randomized/L06UniversalCollisionCount.lean

Introduction "A universal hash-family certificate already controls the number
of colliding hash functions for every distinct pair of keys. Specialize it to
one pair."

Statement (κ : Type) (buckets : Nat) (family : List (κ → Fin buckets)) :
    UniversalHashFamily family → ∀ x y : κ, x ≠ y →
      buckets * (family.filter (fun hash => hash x == hash y)).length ≤ family.length := by
  Hint "Apply the universal-family hypothesis to the chosen keys."
  exact fun h_family x y hxy => h_family x y hxy

Conclusion "The universal-hashing count bound now applies to any chosen pair."

NewDefinition Game.Randomized.UniversalHashFamily
