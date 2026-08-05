import Game.Metadata
import Game.Support.Design

open Game.Design

World "Strings"
Level 2
Title "Rolling Hash Properties"
-- source: RequestProject Lab10.hashList_append_singleton, Lab10.hashList_eq_of_eq

Introduction "Rabin–Karp fingerprints a window with a rolling polynomial
hash. Prove its two basic properties: appending one character updates the
hash by a single multiply-add, and equal blocks always hash equal."

Statement (B : ℕ) (l : List ℕ) (c : ℕ) (l₁ l₂ : List ℕ) (h : l₁ = l₂) :
    hashList B (l ++ [c]) = hashList B l * B + c ∧ hashList B l₁ = hashList B l₂ := by
  Hint "Prove the two facts separately; the first unfolds `hashList` as a
  fold, the second is immediate from `h`."
  constructor
  · unfold hashList
    Hint (hidden := true) "`rw [List.foldl_append, List.foldl_cons, List.foldl_nil]`."
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  · rw [h]

Conclusion "Verified: the rolling hash updates incrementally and respects equality."

NewDefinition Game.Design.hashList
NewTheorem List.foldl_append List.foldl_cons List.foldl_nil
