import Mathlib

/-! Basic graph definitions used by the Graphs world. These are intentionally
small relation-level models: enough to state traversal, shortest-path,
relaxation, cut, and union-find invariants without committing later phases to a
specific executable graph representation. -/
namespace Game.Graph

/-- A directed graph represented by its edge relation. -/
abbrev DirectedGraph (V : Type*) := V → V → Prop

/-- Reachability from a fixed source through zero or more directed edges. -/
inductive Reach {V : Type*} (edge : DirectedGraph V) (source : V) : V → Prop
  | refl : Reach edge source source
  | tail {u v} : Reach edge source u → edge u v → Reach edge source v

/-- Every queued vertex has already been discovered by a path from the source. -/
def QueueInvariant {V : Type*} (edge : DirectedGraph V) (source : V) (queue : List V) : Prop :=
  ∀ v ∈ queue, Reach edge source v

/-- An unweighted path with an explicit edge count. -/
inductive PathLength {V : Type*} (edge : DirectedGraph V) : V → V → Nat → Prop
  | nil (v) : PathLength edge v v 0
  | cons {u v z n} : edge u v → PathLength edge v z n → PathLength edge u z (n + 1)

/-- `n` is a shortest unweighted-path length from `source` to `target`. -/
def IsShortest {V : Type*} (edge : DirectedGraph V) (source target : V) (n : Nat) : Prop :=
  PathLength edge source target n ∧ ∀ m, PathLength edge source target m → n ≤ m

/-- A list is topologically ordered when every edge between listed vertices points forward. -/
def IsTopological {V : Type*} [BEq V] (edge : DirectedGraph V) (order : List V) : Prop :=
  ∀ ⦃u v⦄, u ∈ order → v ∈ order → edge u v → order.idxOf u < order.idxOf v

/-- Mutual reachability, the mathematical specification of an SCC. -/
def StronglyConnected {V : Type*} (edge : DirectedGraph V) (u v : V) : Prop :=
  Reach edge u v ∧ Reach edge v u

/-- A tentative-distance relaxation along one weighted edge. -/
def relax (du dv weight : Nat) : Nat := min dv (du + weight)

/-- Floyd-Warshall's single-intermediate update. -/
def floydUpdate (direct viaLeft viaRight : Nat) : Nat :=
  min direct (viaLeft + viaRight)

/-- A cut represented by membership in its left shore. -/
def CrossesCut {V : Type*} (left : Set V) (u v : V) : Prop :=
  (u ∈ left ∧ v ∉ left) ∨ (v ∈ left ∧ u ∉ left)

/-- `e` is a light edge crossing a cut. -/
def IsLightCutEdge {V : Type*} (weight : V → V → Nat) (left : Set V) (u v : V) : Prop :=
  CrossesCut left u v ∧ ∀ x y, CrossesCut left x y → weight u v ≤ weight x y

/-- A compact union-find model: equal labels mean equal representatives. -/
def SameRepresentative {V R : Type*} (repr : V → R) (u v : V) : Prop := repr u = repr v

/-- Union the classes of `a` and `b` by relabelling all members of `b`'s class. -/
def unionLabels [DecidableEq R] (repr : V → R) (a b : V) : V → R :=
  fun x => if repr x = repr b then repr a else repr x

end Game.Graph
