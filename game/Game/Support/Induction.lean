import Mathlib

/-! Answer-free definitions and given (already-proven) facts used by the
Contracts world's structural-induction levels. Ported from the course's
`RequestProject/Lab02StructuralInduction.lean`. Theorems here are either
prerequisites a later level's proof is allowed to cite (because an earlier
level already played them), or genuinely out-of-scope infrastructure — the
level files themselves still perform the actual induction the lab teaches.
No level solutions live here. -/
namespace Game.Induction

/-! ## Arithmetic expressions (`AExp`) -/

/-- Arithmetic expressions over integer-valued variables. -/
inductive AExp where
  /-- An integer constant. -/
  | const : Int → AExp
  /-- A program variable. -/
  | var   : String → AExp
  /-- The sum of two expressions. -/
  | plus  : AExp → AExp → AExp

/-- A *state* assigns an integer value to every variable name. -/
abbrev State := String → Int

/-- The value (semantics) of an expression in a given state. -/
def aval : AExp → State → Int
  | .const n,  _ => n
  | .var x,    s => s x
  | .plus a b, s => aval a s + aval b s

/-- Fold sub-expressions whose operands are already constants. -/
def asimpConst : AExp → AExp
  | .const n => .const n
  | .var x   => .var x
  | .plus a b =>
      match asimpConst a, asimpConst b with
      | .const m, .const n => .const (m + n)
      | a',       b'       => .plus a' b'

/-- Smart `plus`: fold two constants, and simplify adding the constant `0`. -/
def plusSmart : AExp → AExp → AExp
  | .const m, .const n => .const (m + n)
  | .const m, b        => if m = 0 then b else .plus (.const m) b
  | a,        .const n => if n = 0 then a else .plus a (.const n)
  | a,        b        => .plus a b

/-! ## Lists

A hand-rolled list type under `Game.Induction.List`, so the base/step shape
of structural induction is completely explicit. -/

/-- A hand-rolled singly-linked list. -/
inductive List (α : Type u) where
  /-- The empty list. -/
  | nil  : List α
  /-- Prepend an element to a list. -/
  | cons : α → List α → List α

namespace List

/-- Append (concatenate) two lists. -/
def append : List α → List α → List α
  | nil,       ys => ys
  | cons x xs, ys => cons x (append xs ys)

/-- The length of a list. -/
def len : List α → Nat
  | nil       => 0
  | cons _ xs => len xs + 1

/-- Reverse a list. -/
def rev : List α → List α
  | nil       => nil
  | cons x xs => append (rev xs) (cons x nil)

/-- **Given**: `nil` is a right identity for `append`. Played in the "List
Append Identity" level; supplied here so later levels can cite it directly. -/
theorem append_nil (xs : List α) : append xs nil = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [append, ih]

/-- **Given**: append is associative. Played in the "List Append
Associative" level; supplied here so "List Reverse Append" can cite it
directly. -/
theorem append_assoc (xs ys zs : List α) : append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [append, append, append, ih]

/-- **Given**: reversing an append reverses the order of the parts. Played
in the "List Reverse Append" level; supplied here so "Reverse Is Involutive"
can cite it directly. -/
theorem rev_append (xs ys : List α) : rev (append xs ys) = append (rev ys) (rev xs) := by
  induction xs with
  | nil => rw [append, rev, append_nil]
  | cons x xs ih => rw [append, rev, ih, rev, append_assoc]

/-- **Given**: length distributes over append. Played in the "List Append Length"
level; supplied here so "Tree Inorder Length" can cite it directly. -/
theorem len_append (xs ys : List α) : len (append xs ys) = len xs + len ys := by
  induction xs with
  | nil => rw [append, len, Nat.zero_add]
  | cons x xs ih => rw [append, len, len, ih]; omega

end List

/-! ## Binary trees (`Tree`) -/

/-- Binary trees carrying a value of type `α` at each internal node. -/
inductive Tree (α : Type u) where
  /-- An empty tree. -/
  | leaf : Tree α
  /-- A node with a left subtree, a value, and a right subtree. -/
  | node : Tree α → α → Tree α → Tree α

namespace Tree

/-- Number of internal nodes. -/
def size : Tree α → Nat
  | leaf       => 0
  | node l _ r => size l + size r + 1

/-- Height (longest root-to-leaf path). -/
def height : Tree α → Nat
  | leaf       => 0
  | node l _ r => max (height l) (height r) + 1

/-- Mirror image: swap the two children at every node. -/
def mirror : Tree α → Tree α
  | leaf       => leaf
  | node l x r => node (mirror r) x (mirror l)

/-- **Given**: mirroring twice gives back the original tree. Played in the
"Tree Mirror Involutive" level; supplied here so later levels can cite it
directly. -/
theorem mirror_mirror (t : Tree α) : mirror (mirror t) = t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => rw [mirror, mirror, ihl, ihr]

/-- **Given**: mirroring preserves the number of nodes. Played in the
"Tree Mirror Preserves Size" level; supplied here so later levels can cite it
directly. -/
theorem size_mirror (t : Tree α) : size (mirror t) = size t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    rw [mirror, size, size, ihl, ihr]
    omega

/-- In-order traversal, producing an `List`. -/
def inorder : Tree α → List α
  | leaf       => List.nil
  | node l x r => List.append (inorder l) (List.cons x (inorder r))

end Tree

end Game.Induction
