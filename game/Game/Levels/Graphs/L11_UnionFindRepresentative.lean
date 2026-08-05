import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 11
Title "Union-Find Representative"

Introduction "In this compact union-find model, a union relabels everything in
`b`'s class to use `a`'s representative. In particular, `a` and `b` have the
same representative after the union."

Statement {V R : Type*} [DecidableEq R] (repr : V → R) (a b : V) :
    SameRepresentative (unionLabels repr a b) a b := by
  Hint "Unfold both definitions. The label for `b` is rewritten to `repr a` by
  the true branch of the `if`."
  unfold SameRepresentative unionLabels
  aesop

Conclusion "The union operation makes the chosen vertices share a
representative."

NewTactic unfold aesop
NewDefinition Game.Graph.SameRepresentative Game.Graph.unionLabels
