import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 7
Title "Z-Box Bound"

Introduction "The Z value at `position` measures a common prefix against the
suffix starting there, so it can never exceed how much text is left. Prove
the general fact that a common-prefix length never exceeds the length of its
second argument, then specialize it to the suffix starting at `position`."

Statement {α : Type} [DecidableEq α] (text : List α) (position : Nat) :
    zValue text position ≤ text.length - position := by
  Hint "Unfold `zValue`, then establish the general auxiliary fact
  `∀ xs ys, commonPrefixLength xs ys ≤ ys.length` by induction on `xs`."
  unfold zValue
  have hgen : ∀ (xs ys : List α), commonPrefixLength xs ys ≤ ys.length := by
    intro xs
    induction xs with
    | nil =>
      intro ys
      have : commonPrefixLength ([] : List α) ys = 0 := rfl
      omega
    | cons x xs ih =>
      intro ys
      cases ys with
      | nil =>
        have h1 : commonPrefixLength (x :: xs) ([] : List α) = 0 := rfl
        have h2 : ([] : List α).length = 0 := rfl
        omega
      | cons y ys =>
        by_cases hxy : x = y
        · subst hxy
          have step : commonPrefixLength (x :: xs) (x :: ys) =
              commonPrefixLength xs ys + 1 := if_pos rfl
          have hlen : (x :: ys).length = ys.length + 1 := rfl
          have hle := ih ys
          omega
        · have step : commonPrefixLength (x :: xs) (y :: ys) = 0 := if_neg hxy
          omega
  Hint (hidden := true) "Apply `hgen` at `text` and `text.drop position`, then
  bridge `(text.drop position).length` to `text.length - position` with
  `List.length_drop`."
  simpa [List.length_drop] using hgen text (text.drop position)

Conclusion "A Z-box can never overrun the text it inspects."

NewDefinition Game.String.zValue
NewTheorem List.length_drop
