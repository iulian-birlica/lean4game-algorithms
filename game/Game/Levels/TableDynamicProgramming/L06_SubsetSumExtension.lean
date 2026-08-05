import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 6
Title "Subset-Sum Extension"

Introduction "A subset-sum table entry is a concrete witness: a chosen sublist
with the requested sum. If `items` can make `target`, then adding a new item to
both the available list and the target preserves the witness."

/-- Prefixing the chosen subset extends a subset-sum witness by the same item. -/
Statement (items : List Nat) (item target : Nat)
    (h : HasSubsetSum items target) :
    HasSubsetSum (item :: items) (item + target) := by
  Hint "Unpack `HasSubsetSum` to get the chosen sublist and its sum equation,
  then prefix that chosen list by `item`."
  rcases h with ⟨chosen, hsub, hsum⟩
  refine ⟨item :: chosen, ?_, ?_⟩
  · exact hsub.cons₂ item
  · simp [hsum]

Conclusion "The subset-sum witness extends to the next table row."

NewTactic exact rcases refine simp
NewDefinition Game.TableDP.HasSubsetSum
NewTheorem List.Sublist.cons₂
