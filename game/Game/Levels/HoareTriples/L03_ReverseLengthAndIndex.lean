import Game.Metadata
import Game.Support.Contracts

World "HoareTriples"
Level 3
Title "Reverse Length and Index"
-- source: RequestProject Lab01.reverse_spec (ported from game W01-L03)

Introduction "Prove the `reverse` contract: the result has the same length,
and reading it at index `i` matches reading the original from the other end."

Statement {T : Type} (values : List T) :
    (Game.Contracts.reverse values).length = values.length ∧
    (∀ (i : Nat) (h : i < (Game.Contracts.reverse values).length),
      (Game.Contracts.reverse values)[i] = values[values.length - 1 - i]'(by
        unfold Game.Contracts.reverse at h
        rw [List.length_reverse] at h
        omega)) := by
  Hint "Prove the length and the indexing property separately."
  refine ⟨?_, ?_⟩
  · Hint (hidden := true) "Use `List.length_reverse`."
    unfold Game.Contracts.reverse
    rw [List.length_reverse]
  · intro i h
    Hint (hidden := true) "Use `List.getElem_reverse`."
    unfold Game.Contracts.reverse at h ⊢
    rw [List.getElem_reverse]

Conclusion "Mirror confirmed: length preserved, indices reflected correctly."

NewTactic unfold refine
NewDefinition Game.Contracts.reverse
NewTheorem List.length_reverse List.getElem_reverse
