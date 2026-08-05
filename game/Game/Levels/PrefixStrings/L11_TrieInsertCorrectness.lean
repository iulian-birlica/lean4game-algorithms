import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 11
Title "Trie Insert Correctness"

Introduction "Inserting a word must make it findable again. At the empty
word, insertion just flips the terminal flag at the current node. At a head
symbol `x`, insertion updates the child at key `x` and recurses — looking
that child back up is exactly what the induction hypothesis proves."

Statement {α : Type} [DecidableEq α] (word : List α) (trie : Trie α) :
    Trie.lookup word (Trie.insert word trie) = true := by
  Hint "Induct on `word`, generalizing the trie so the induction hypothesis
  applies to every child trie encountered."
  induction word generalizing trie with
  | nil =>
    cases trie with
    | node terminal children => rfl
  | cons x xs ih =>
    cases trie with
    | node terminal children =>
      Hint (hidden := true) "Unfold one insertion step: the child at key `x`
      is updated to `Trie.insert xs (children x |>.getD Trie.empty)`, and the
      lookup finds exactly that update. Close with the induction hypothesis."
      simp [Trie.insert, Trie.lookup]
      exact ih _

Conclusion "Every inserted word is found again."
