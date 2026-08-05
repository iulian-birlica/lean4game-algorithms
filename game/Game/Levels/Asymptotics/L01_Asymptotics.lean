import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Asymptotics"
Level 1
Title "Asymptotics"

Introduction "Asymptotic analysis ignores small inputs and constant factors so
we can compare the eventual shape of two cost functions. In this first room,
you prove the simplest eventual bound directly: after input size `0`, the
function `n ↦ n` is bounded by itself."

/-- The identity cost function is eventually bounded by itself. -/
Statement : (fun n : ℕ => (n : ℝ)) =O (fun n : ℕ => (n : ℝ)) := by
  Hint "Unfold Big-O directly. Witness `C = 1` and `N = 0`."
  use 1, by norm_num, 0
  norm_num

Conclusion "Asymptotic comparison begins with reflexivity: every cost is
bounded by itself."

NewTactic use norm_num
NewDefinition Game.Clockwork.IsBigO
