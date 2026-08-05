import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.git "https://github.com/leanprover-community/lean4game.git" leanVersion "server"
  version? := s!"git#{leanVersion}"
  opts := ∅
}

open Lean in
#eval (do
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env ``RemoteGameServer)
  : Elab.Command.CommandElabM Unit)

require "leanprover-community" / mathlib @ git leanVersion

/-!
# PACKAGE CONFIGURATION

NOTE: The `leanOptions` and `moreServerOptions` influence how the player perceives the game.
`linter.all` must be `false` to prevent linter warnings from showing up during play.
`maxHeartbeats`/`maxRecDepth` are raised because the course proofs this game is built from
are heavy (see the reference course's `Main.lean`, which sets the same values).
-/
package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩,
    ⟨`pp.showLetValues, true⟩,
    ⟨`tactic.hygienic, false⟩,
    ⟨`maxHeartbeats, 8000000⟩,
    ⟨`maxRecDepth, 4000⟩]
  moreLeanArgs := #[
    "-Dtrace.debug=false"]
  moreServerOptions := #[
    ⟨`trace.debug, true⟩]

@[default_target]
lean_lib Game
