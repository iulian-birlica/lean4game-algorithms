import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 2
Title "Knapsack Recurrence"
-- source: RequestProject Lab06.knap_tail_le

Introduction "Unlike the continuous knapsack, items here are taken whole or
not at all — the greedy densest-first rule fails, so we need the DP
recurrence `knap`. Its most basic property: dropping the head item can only
decrease the achievable value (skipping it is always an option)."

Statement (it : KItem) (rest : List KItem) (c : ℕ) :
    knap rest c ≤ knap (it :: rest) c := by
  Hint "Case on whether the head item fits; either way, unfold `knap` and
  compare with the supremum."
  Hint (hidden := true) "`simp [knap, h, ↓reduceIte, le_sup_left, le_refl]` after the
  `by_cases`."
  by_cases h : it.w ≤ c <;> simp +decide only [knap, h, ↓reduceIte, le_sup_left, le_refl]

Conclusion "Confirmed: the recurrence never loses value by skipping an item."

NewTheorem le_sup_left
