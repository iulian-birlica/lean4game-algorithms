import Mathlib

/-! Search trees, AVL balance, chained hash tables, and path compression used
by the Data Structures world. -/
namespace Game.DataStructures

inductive SearchTree where
  | nil
  | node (left : SearchTree) (key : Nat) (right : SearchTree)
  deriving DecidableEq

namespace SearchTree

/-- In-order traversal of a search tree. -/
def inorder : SearchTree → List Nat
  | .nil => []
  | .node left key right => inorder left ++ key :: inorder right

/-- Dictionary lookup. -/
def lookup (target : Nat) : SearchTree → Bool
  | .nil => false
  | .node left key right =>
      if target < key then lookup target left
      else if key < target then lookup target right
      else true

/-- Insert a key, leaving an existing copy unchanged. -/
def insert (target : Nat) : SearchTree → SearchTree
  | .nil => .node .nil target .nil
  | .node left key right =>
      if target < key then .node (insert target left) key right
      else if key < target then .node left key (insert target right)
      else .node left key right

/-- Every key stored in a tree satisfies a predicate. -/
def All (p : Nat → Prop) : SearchTree → Prop
  | .nil => True
  | .node left key right => p key ∧ All p left ∧ All p right

/-- The strict binary-search-tree invariant. -/
def IsBST : SearchTree → Prop
  | .nil => True
  | .node left key right =>
      All (· < key) left ∧ All (key < ·) right ∧ IsBST left ∧ IsBST right

/-- Every key bounded by a predicate over a whole tree is bounded over its
in-order traversal. Reused for both the left- and right-subtree bounds that
`IsBST` carries at each node. -/
theorem forall_mem_inorder_of_all {p : Nat → Prop} :
    ∀ (t : SearchTree), All p t → ∀ x ∈ inorder t, p x := by
  intro t
  induction t with
  | nil => intro _ x hx; simp [inorder] at hx
  | node left key right ih_left ih_right =>
      intro h x hx
      obtain ⟨hkey, hleft, hright⟩ := h
      simp only [inorder, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · exact ih_left hleft x hx
      · subst hx; exact hkey
      · exact ih_right hright x hx

end SearchTree

namespace AVL

open SearchTree

/-- A single right rotation. Trees without the required left child are left
unchanged. -/
def rotateRight : SearchTree → SearchTree
  | .node (.node a x b) y c => .node a x (.node b y c)
  | tree => tree

/-- A single left rotation. Trees without the required right child are left
unchanged. -/
def rotateLeft : SearchTree → SearchTree
  | .node a x (.node b y c) => .node (.node a x b) y c
  | tree => tree

/-- Height of a search tree. -/
def height : SearchTree → Nat
  | .nil => 0
  | .node left _ right => max (height left) (height right) + 1

/-- The structural AVL balance condition. -/
def Balanced : SearchTree → Prop
  | .nil => True
  | .node left _ right =>
      height left ≤ height right + 1 ∧ height right ≤ height left + 1 ∧
        Balanced left ∧ Balanced right

/-- An AVL tree combines search ordering with height balance. -/
def IsAVL (tree : SearchTree) : Prop := tree.IsBST ∧ Balanced tree

end AVL

/-- A chained hash table is a family of buckets indexed by hash values. -/
abbrev HashTable (α : Type) := Nat → List α

namespace HashTable

variable {α : Type} [DecidableEq α]

/-- The empty table has no entries in any bucket. -/
def empty : HashTable α := fun _ => []

/-- Lookup checks the bucket selected by the hash function. -/
def lookup (hash : α → Nat) (x : α) (table : HashTable α) : Prop :=
  x ∈ table (hash x)

/-- Chained insertion adds the key at the front of its bucket. -/
def insert (hash : α → Nat) (x : α) (table : HashTable α) : HashTable α :=
  Function.update table (hash x) (x :: table (hash x))

/-- Rebuild a table from a finite key list, as during resizing or rehashing. -/
def rebuild (hash : α → Nat) (keys : List α) : HashTable α :=
  keys.foldr (insert hash) empty

/-- Rebuilding unfolds one key at a time: rebuild the tail, then insert the head. -/
theorem rebuild_cons (hash : α → Nat) (a : α) (keys : List α) :
    rebuild hash (a :: keys) = insert hash a (rebuild hash keys) := rfl

/-- After inserting `a`, a lookup for `x` succeeds exactly when `x` is the
newly inserted key or was already present. -/
theorem lookup_insert_iff (hash : α → Nat) (a x : α) (table : HashTable α) :
    lookup hash x (insert hash a table) ↔ x = a ∨ lookup hash x table := by
  show x ∈ Function.update table (hash a) (a :: table (hash a)) (hash x) ↔
    x = a ∨ x ∈ table (hash x)
  by_cases h : hash x = hash a
  · rw [Function.update_apply, if_pos h, h, List.mem_cons]
  · rw [Function.update_apply, if_neg h]
    have hxa : x ≠ a := fun heq => h (congrArg hash heq)
    simp [hxa]

end HashTable

namespace HashLoad

open HashTable

variable {α : Type} [DecidableEq α]

/-- Total number of stored entries in the first `bucketCount` buckets. -/
def entryCount (bucketCount : Nat) (table : HashTable α) : Nat :=
  ((List.range bucketCount).map fun bucket => (table bucket).length).sum

/-- The cross-multiplied load-factor bound
`entries / buckets <= numerator / denominator`. -/
def LoadAtMost (bucketCount numerator denominator : Nat)
    (table : HashTable α) : Prop :=
  denominator * entryCount bucketCount table <= numerator * bucketCount

end HashLoad

/-- Parent pointers accompanied by their abstract representative map. -/
structure DisjointSet (V : Type) where
  parent : V → V
  representative : V → V
  parent_same_class : ∀ x, representative (parent x) = representative x
  representative_idem : ∀ x, representative (representative x) = representative x

namespace DisjointSet

variable {V : Type} [DecidableEq V]

/-- Compress one parent pointer directly to its class representative. -/
def compress (set : DisjointSet V) (x : V) : DisjointSet V where
  parent := Function.update set.parent x (set.representative x)
  representative := set.representative
  parent_same_class := by
    intro y
    by_cases h : y = x
    · subst h
      rw [Function.update_self]
      exact set.representative_idem y
    · rw [Function.update_of_ne h]
      exact set.parent_same_class y
  representative_idem := set.representative_idem

end DisjointSet

end Game.DataStructures
