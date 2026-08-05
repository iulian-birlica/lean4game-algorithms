import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 10
Title "Undecidability Transport"
-- source: ../game/Game/Worlds/W08Computability/L03UndecidabilityTransport.lean

Introduction "A many-one reduction cannot make an undecidable problem decidable. If
`source` reduces to `target`, then a decider for `target` would pull back to a decider for
`source`."

Statement {α β : Type*} [Primcodable α] [Primcodable β]
    {source : α → Prop} {target : β → Prop}
    (hred : ManyOne source target) (hsource : ¬ ComputablePred source) :
    ¬ ComputablePred target := by
  Hint "Use the packaged theorem `undecidable_of_manyOne`."
  exact undecidable_of_manyOne hred hsource

Conclusion "Verified: undecidability moves forward along many-one reductions."

NewTheorem Game.Complexity.undecidable_of_manyOne
