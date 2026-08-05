import Game.Support.Graph

namespace Game.TableDP

/-- One edit-distance table update. The three arguments are the costs after
deletion, insertion, and substitution, before paying for the edit. -/
def editUpdate (deletion insertion substitution : Nat) : Nat :=
  min (deletion + 1) (min (insertion + 1) substitution)

/-- An explicit edit-alignment relation. Its index counts insertions,
deletions, and substitutions; matching equal symbols is free. -/
inductive AlignmentCost {α : Type*} : List α → List α → Nat → Prop
  /-- Empty lists align at zero cost. -/
  | nil : AlignmentCost [] [] 0
  /-- Matching equal heads preserves the existing alignment cost. -/
  | match (a : α) {xs ys n} : AlignmentCost xs ys n →
      AlignmentCost (a :: xs) (a :: ys) n
  /-- Deleting one source symbol increases the alignment cost by one. -/
  | delete (a : α) {xs ys n} : AlignmentCost xs ys n →
      AlignmentCost (a :: xs) ys (n + 1)
  /-- Inserting one target symbol increases the alignment cost by one. -/
  | insert (a : α) {xs ys n} : AlignmentCost xs ys n →
      AlignmentCost xs (a :: ys) (n + 1)
  /-- Substituting one symbol for another increases the alignment cost by one. -/
  | substitute (a b : α) {xs ys n} : AlignmentCost xs ys n →
      AlignmentCost (a :: xs) (b :: ys) (n + 1)

/-- Declarative specification for a successful subset-sum table entry. -/
def HasSubsetSum (items : List Nat) (target : Nat) : Prop :=
  ∃ chosen : List Nat, chosen.Sublist items ∧ chosen.sum = target

/-- A matrix-chain candidate combines two optimal subintervals and the scalar
multiplication cost at their split. -/
def matrixSplitCost (left right rows middle cols : Nat) : Nat :=
  left + right + rows * middle * cols

/-- Choose the better of the current matrix-chain candidate and a new split. -/
def improveMatrixChain (current candidate : Nat) : Nat :=
  min current candidate

/-- One Floyd-Warshall table layer, expressed pointwise over a distance table. -/
def floydLayer {V : Type*} (previous : V → V → Nat) (k : V) : V → V → Nat :=
  fun i j => Game.Graph.floydUpdate (previous i j) (previous i k) (previous k j)

/-- A list is a strictly increasing candidate for longest increasing subsequence. -/
def StrictlyIncreasing (xs : List Nat) : Prop :=
  xs.Pairwise (· < ·)

/-- Two implementations compute the same DP table extensionally. -/
def SameTable {ι α : Type*} (memo tabulation : ι → α) : Prop :=
  ∀ i, memo i = tabulation i

end Game.TableDP
