import GameServer
import Mathlib.Tactic
import Game.Doc.Tactics
import Game.Doc.Theorems

/-! Shared imports available to every level. `Game.lean` must exist and end with
`MakeGame`; beyond that the project layout is free, but each world's levels
must be imported from exactly one file, in level order, to avoid a known
lean4game import-order bug. -/
