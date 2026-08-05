import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L13_BigOClosure

open Game.Clockwork

World "Asymptotics"
Level 14
Title "Big-Theta Definition"
-- source: RequestProject Lab11.IsBigTheta.symm, Lab11.IsBigTheta.trans

Introduction "`f =Θ g` (`f` and `g` grow at exactly the same rate) is defined
as `f =O g ∧ g =O f`. Show it is symmetric and transitive — together with
reflexivity (free from `IsBigO.refl`), `=Θ` is an equivalence relation."

/-- Big-Theta is symmetric and transitive. -/
Statement bigTheta_calculus (f g h : ℕ → ℝ) :
    (f =Θ g → g =Θ f) ∧ (f =Θ g → g =Θ h → f =Θ h) := by
  Hint "Both directions are immediate from the pair — swap it, or combine
  `=O`-transitivity on each side."
  constructor
  · intro hfg
    exact ⟨hfg.2, hfg.1⟩
  · Hint (hidden := true) "Use the transitivity part of `bigO_calculus` once for `f =O h`, and once for `h =O f`."
    intro hfg hgh
    exact ⟨
      (bigO_calculus (f := f) (g := g) (h := h)).2 hfg.1 hgh.1,
      (bigO_calculus (f := h) (g := g) (h := f)).2 hgh.2 hfg.2
    ⟩

Conclusion "Verified: `=Θ` is a genuine equivalence relation on growth rates."

NewDefinition Game.Clockwork.IsBigTheta
NewTheorem bigO_calculus bigTheta_calculus
