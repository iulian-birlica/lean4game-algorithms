import Game.Support.PrefixStrings

/-! Answer-free definitions for suffix enumeration, longest-common-prefix
measurements, and suffix-array certificates. The certificate separates the
permutation requirement from lexicographic ordering, so levels can exercise
each invariant independently. Ported from the older game tree. -/
namespace Game.AdvancedString

open Game.String

/-- The suffix of `text` beginning at position `i`. Position `text.length`
denotes the empty suffix. -/
def suffix {α : Type} (text : List α) (i : Nat) : List α :=
  text.drop i

/-- All valid suffix starting positions, including the empty suffix. -/
def suffixIndices {α : Type} (text : List α) : List Nat :=
  List.range (text.length + 1)

/-- The suffixes in their original text order, including the empty suffix. -/
def suffixes {α : Type} (text : List α) : List (List α) :=
  (suffixIndices text).map (suffix text)

/-- A non-strict lexicographic relation induced by a strict symbol order. -/
def LexLE {α : Type} (lt : α → α → Prop) : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => lt x y ∨ (x = y ∧ LexLE lt xs ys)

/-- The longest-common-prefix value used by suffix-array LCP tables. -/
def lcp {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  commonPrefixLength xs ys

/-- A suffix-array certificate: every valid suffix position occurs exactly
once, and the listed suffixes are in lexicographic order. -/
def IsSuffixArray {α : Type} (lt : α → α → Prop)
    (text : List α) (order : List Nat) : Prop :=
  order.Perm (suffixIndices text) ∧
    order.Pairwise (fun i j => LexLE lt (suffix text i) (suffix text j))

end Game.AdvancedString
