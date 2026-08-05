import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 5
Title "Prefix Characterization"

Introduction "The previous level measured a known prefix. Now go the other
way: if the common-prefix scan reaches all the way to `xs`'s own length, `xs`
really must be a prefix of `ys` — the scan couldn't have gotten that far
otherwise. Induct on `xs`, generalizing `ys`."

Statement {α : Type} [DecidableEq α] (xs ys : List α) :
    commonPrefixLength xs ys = xs.length → IsPrefix xs ys := by
  Hint "Induct on `xs`, generalizing `ys`, then `intro` the hypothesis inside
  each case."
  induction xs generalizing ys with
  | nil => intro _; exact ⟨ys, rfl⟩
  | cons x xs ih =>
    intro h
    Hint (hidden := true) "Case on `ys`: if it's empty the hypothesis is
    already false; otherwise compare the two heads."
    cases ys with
    | nil => simp [commonPrefixLength] at h
    | cons y ys =>
      by_cases hxy : x = y
      · subst hxy
        Hint (hidden := true) "With matching heads, simplify `h` down to the
        tails' equation and apply the induction hypothesis to it."
        simp [commonPrefixLength] at h
        obtain ⟨rest, rfl⟩ := ih ys h
        exact ⟨rest, rfl⟩
      · simp [commonPrefixLength, hxy] at h

Conclusion "Reaching full length is exactly what it takes to be a prefix."
