import Mathlib

/-! Answer-free definitions used by the randomized-algorithms world. Ported
from the older game tree and adapted to the current project layout. -/
namespace Game.Randomized

/-- Number of seeds on which an event succeeds. -/
def eventCount (seeds : List σ) (event : σ → Bool) : Nat :=
  (seeds.filter event).length

/-- Probability of an event in a finite uniform experiment. The empty
experiment has probability zero. -/
def probability (seeds : List σ) (event : σ → Bool) : ℚ :=
  if seeds.isEmpty then 0 else eventCount seeds event / seeds.length

/-- Expected value of a rational-valued random variable on a finite uniform
experiment. The empty experiment has expectation zero. -/
def expectation (seeds : List σ) (value : σ → ℚ) : ℚ :=
  if seeds.isEmpty then 0 else (seeds.map value).sum / seeds.length

/-- A Las Vegas algorithm is always correct; randomness may still affect cost. -/
def LasVegas (seeds : List σ) (run : σ → α) (good : α → Prop) : Prop :=
  ∀ seed ∈ seeds, good (run seed)

/-- A Monte Carlo algorithm may fail, but with bounded error probability. -/
def MonteCarlo (seeds : List σ) (run : σ → α) (good : α → Bool)
    (error : ℚ) : Prop :=
  probability seeds (fun seed => !good (run seed)) ≤ error

/-- Collision of two keys under one hash function. -/
def Collides {κ : Type} (hash : κ → Fin buckets) (x y : κ) : Prop :=
  hash x = hash y

/-- A finite hash family is universal when at most a `1 / buckets` fraction of
its members collide on each pair of distinct keys. The cross-multiplied form
avoids division and also handles the empty family cleanly. -/
def UniversalHashFamily {κ : Type} (family : List (κ → Fin buckets)) : Prop :=
  ∀ x y, x ≠ y →
    buckets * (family.filter (fun hash => hash x == hash y)).length ≤ family.length

/-- Probability that positions `i < j` are directly compared by randomized
quicksort. Among the `j - i + 1` elements in their interval, one endpoint must
be chosen first. -/
def quicksortPairProbability (i j : Nat) : ℚ :=
  2 / (j - i + 1)

/-- Harmonic numbers used in the standard quicksort analysis. -/
def harmonic : Nat → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / (n + 1)

/-- A convenient harmonic upper bound for randomized quicksort comparisons. -/
def quicksortExpectedComparisons (n : Nat) : ℚ :=
  2 * n * harmonic n

/-- A geometric recurrence modeling randomized selection: one linear partition
round, then half of the remaining unresolved work in expectation. -/
def selectionExpectedWork : Nat → ℚ
  | 0 => 0
  | n + 1 => n + 1 + selectionExpectedWork n / 2

end Game.Randomized
