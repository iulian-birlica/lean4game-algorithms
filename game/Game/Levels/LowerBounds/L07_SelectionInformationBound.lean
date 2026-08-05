import Game.Metadata
import Game.Support.LowerBounds

open Game.LowerBounds

World "LowerBounds"
Level 7
Title "Selection Information Bound"
-- source: ../game/Game/Worlds/W14LowerBounds/L07SelectionInformationBound.lean

Introduction "A procedure that distinguishes all `candidates` using
`outcomes`-ary answers and `queries` steps needs at least as many transcripts
as candidates."

Statement (candidates outcomes queries : Nat)
    (encode : Fin candidates → Transcript outcomes queries) :
    Separates encode → candidates ≤ outcomes ^ queries := by
  Hint "Apply the same injective-cardinality bound, now with `Fin candidates`
  as the hidden space."
  intro h
  have hcard := Fintype.card_le_of_injective encode h
  simpa using hcard

Conclusion "Information alone forces a lower bound on the number of queries."
