import Game.Metadata
import Game.Support.Design

open Game.Design
open List

World "Sequences"
Level 2
Title "LCS Correctness"
-- source: RequestProject Lab07.lcs_spec

Introduction "**Packaged specification.** `lcs xs ys` is a common
subsequence of `xs` and `ys` of *maximum* length — the two feasibility
facts, plus a supplied optimality theorem. Assemble the full contract."

Statement {α : Type} [DecidableEq α] (xs ys : List α) :
    (lcs xs ys <+ xs) ∧ (lcs xs ys <+ ys) ∧
      (∀ zs : List α, zs <+ xs → zs <+ ys → zs.length ≤ (lcs xs ys).length) := by
  Hint "Pair the two feasibility cards with the supplied optimality card."
  Hint (hidden := true) "`⟨lcs_sublist_left xs ys, lcs_sublist_right xs ys, fun _ hx hy =>
  lcs_length_max xs ys hx hy⟩`."
  exact ⟨lcs_sublist_left xs ys, lcs_sublist_right xs ys, fun _ hx hy => lcs_length_max xs ys hx hy⟩

Conclusion "Verified: `lcs` is provably a longest common subsequence."

NewTheorem Game.Design.lcs_sublist_left Game.Design.lcs_sublist_right
  Game.Design.lcs_length_max
