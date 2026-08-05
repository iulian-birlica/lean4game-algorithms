import Mathlib

/-! Answer-free definitions for prefix, border, and trie reasoning: the shared
measurement (`commonPrefixLength`) underlying both KMP's border/failure
function and the Z-algorithm, plus a small trie for prefix-set membership.
Ported from the older game tree. -/
namespace Game.String

/-- The length of the common prefix of two symbol lists. This is the central
measurement used by both the KMP and Z-algorithm lessons. -/
def commonPrefixLength {α : Type} [DecidableEq α] : List α → List α → Nat
  | x :: xs, y :: ys => if x = y then commonPrefixLength xs ys + 1 else 0
  | _, _ => 0

/-- A word is a prefix when appending some remainder reconstructs the text. -/
def IsPrefix {α : Type} (pre text : List α) : Prop :=
  ∃ rest, text = pre ++ rest

/-- A word is a suffix when prepending some remainder reconstructs the text. -/
def IsSuffix {α : Type} (suffix text : List α) : Prop :=
  ∃ rest, text = rest ++ suffix

/-- A KMP border is simultaneously a prefix and a suffix. -/
def IsBorder {α : Type} (border text : List α) : Prop :=
  IsPrefix border text ∧ IsSuffix border text

/-- The match length inspected by KMP at a candidate starting position. -/
def kmpMatchLength {α : Type} [DecidableEq α]
    (pattern text : List α) (position : Nat) : Nat :=
  commonPrefixLength pattern (text.drop position)

/-- A complete KMP match at a candidate starting position. -/
def KMPMatch {α : Type} [DecidableEq α]
    (pattern text : List α) (position : Nat) : Prop :=
  kmpMatchLength pattern text position = pattern.length

/-- The Z value at `position`: the common-prefix length of the whole text and
the suffix beginning at `position`. -/
def zValue {α : Type} [DecidableEq α] (text : List α) (position : Nat) : Nat :=
  commonPrefixLength text (text.drop position)

/-- Abstract accounting invariant for a linear KMP scan. Successful comparisons
consume text; fallback comparisons spend previously accumulated match length. -/
def WithinKMPBudget (consumed matched comparisons : Nat) : Prop :=
  comparisons + matched ≤ 2 * consumed

/-- **Given**: a word is a prefix of another exactly when their common-prefix
length reaches the whole word — the fact powering both KMP soundness and the
Z-algorithm's full-match test. Played in two directions across "Prefix
Measurement" and "Prefix Characterization"; supplied here so the KMP-soundness
and Z-value levels can assemble it directly. -/
theorem commonPrefixLength_eq_length_iff_isPrefix {α : Type} [DecidableEq α]
    (xs ys : List α) :
    commonPrefixLength xs ys = xs.length ↔ IsPrefix xs ys := by
  constructor
  · induction xs generalizing ys with
    | nil => intro _; exact ⟨ys, rfl⟩
    | cons x xs ih =>
      intro h
      cases ys with
      | nil => simp [commonPrefixLength] at h
      | cons y ys =>
        by_cases hxy : x = y
        · subst hxy
          simp [commonPrefixLength] at h
          obtain ⟨rest, rfl⟩ := ih ys h
          exact ⟨rest, rfl⟩
        · simp [commonPrefixLength, hxy] at h
  · rintro ⟨rest, rfl⟩
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [commonPrefixLength, ih]

/-- A finite trie. Every node records whether a word ends there and stores an
optional child for each possible next symbol. -/
inductive Trie (α : Type) where
  /-- The single trie constructor: whether a word ends here, plus an optional
  child trie per symbol. -/
  | node (terminal : Bool) (children : α → Option (Trie α))

namespace Trie

variable {α : Type} [DecidableEq α]

/-- The empty prefix tree. -/
def empty : Trie α := .node false (fun _ => none)

/-- Membership lookup in a trie. -/
def lookup : List α → Trie α → Bool
  | [], .node terminal _ => terminal
  | x :: xs, .node _ children =>
      match children x with
      | none => false
      | some child => lookup xs child

/-- Insert one word, sharing its prefix with existing branches. -/
def insert : List α → Trie α → Trie α
  | [], .node _ children => .node true children
  | x :: xs, .node terminal children =>
      let child := (children x).getD empty
      .node terminal (Function.update children x (some (insert xs child)))

end Trie

end Game.String
