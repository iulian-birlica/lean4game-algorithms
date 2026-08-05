import Game.Metadata
import Game.Support.LowerBounds

open Game.LowerBounds

World "LowerBounds"
Level 2
Title "Adversary: Two Worlds Remain"
-- source: ../game/Game/Worlds/W14LowerBounds/L02TwoUnqueriedTargets.lean

Introduction "If the complement of the queried set has at least two elements,
the adversary can keep two distinct hidden targets alive."

Statement (α : Type) [Fintype α] [DecidableEq α] (queried : Finset α) :
    queried.card + 2 ≤ Fintype.card α →
      ∃ first second, first ≠ second ∧
        AdversarySurvives queried first ∧ AdversarySurvives queried second := by
  Hint "Show the complement has card at least `2`, then unpack two distinct
  elements with `Finset.one_lt_card`."
  classical
  intro h
  have hcompl : 1 < queriedᶜ.card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨first, hfirst, second, hsecond, hne⟩ := Finset.one_lt_card.mp hcompl
  have hfirst' : AdversarySurvives queried first := by
    simpa [AdversarySurvives] using hfirst
  have hsecond' : AdversarySurvives queried second := by
    simpa [AdversarySurvives] using hsecond
  exact ⟨first, second, hne, hfirst', hsecond'⟩

Conclusion "Two unseen targets remain indistinguishable to the adversary."

NewTheorem Finset.one_lt_card
