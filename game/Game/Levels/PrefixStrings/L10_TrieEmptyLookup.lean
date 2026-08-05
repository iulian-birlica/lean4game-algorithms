import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 10
Title "Empty Trie Lookup"

Introduction "A trie stores words by sharing their prefixes. The empty trie
has no children anywhere, so looking up any nonempty word fails immediately
at the very first symbol."

Statement {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    Trie.lookup (x :: xs) (Trie.empty : Trie α) = false := by
  Hint "Unfold `Trie.empty` and `Trie.lookup`: the empty trie has no child at
  any key, so the lookup fails at the first symbol."
  rfl

Conclusion "Nothing has been inserted, so nothing is found."

NewDefinition Game.String.Trie Game.String.Trie.node Game.String.Trie.empty
  Game.String.Trie.lookup Game.String.Trie.insert
