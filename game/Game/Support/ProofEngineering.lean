import Mathlib

namespace Game.ProofEngineering

/-- A representation invariant for a pair of lists intended to have equal
lengths. -/
def SameLength {α β : Type} (left : List α) (right : List β) : Prop :=
  left.length = right.length

/-- A finite map represented by an association list. -/
abbrev AssocMap (κ ν : Type) := List (κ × ν)

namespace AssocMap

/-- Lookup in an association-list map; the first matching binding wins. -/
def lookup [BEq κ] (key : κ) : AssocMap κ ν → Option ν
  | [] => none
  | (stored, value) :: rest =>
      if key == stored then some value else lookup key rest

/-- Insert a binding at the front of an association-list map. -/
def insert (key : κ) (value : ν) (entries : AssocMap κ ν) : AssocMap κ ν :=
  (key, value) :: entries

end AssocMap

end Game.ProofEngineering
