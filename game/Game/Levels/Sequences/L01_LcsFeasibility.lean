import Game.Metadata
import Game.Support.Design

open Game.Design
open List

World "Sequences"
Level 1
Title "LCS Feasibility"
-- source: RequestProject Lab07.lcs_sublist_left, Lab07.lcs_sublist_right

Introduction "The longest-common-subsequence recurrence `lcs` compares two
lists head by head. Prove it really is a common subsequence of both —
`induction xs, ys using lcs.induct` gives one case per branch of the
recursion."

Statement {α : Type} [DecidableEq α] (xs ys : List α) :
    lcs xs ys <+ xs ∧ lcs xs ys <+ ys := by
  Hint "Prove the two facts separately, each by `induction xs, ys using
  lcs.induct with`."
  constructor
  · induction xs, ys using lcs.induct with
    | case1 x => rw [lcs_nil_left]
    | case2 x hx => rw [lcs_nil_right]; exact List.nil_sublist x
    | case3 xs b ys ih => rw [lcs, if_pos rfl]; exact ih.cons₂ b
    | case4 a xs b ys hab p q hlen ihp ihq => rw [lcs, if_neg hab, if_pos hlen]; exact ihp
    | case5 a xs b ys hab p q hlen ihp ihq =>
        rw [lcs, if_neg hab, if_neg hlen]; exact ihq.trans (List.sublist_cons_self a xs)
  · induction xs, ys using lcs.induct with
    | case1 x => rw [lcs_nil_left]; exact List.nil_sublist x
    | case2 x hx => rw [lcs_nil_right]
    | case3 xs b ys ih => rw [lcs, if_pos rfl]; exact ih.cons₂ b
    | case4 a xs b ys hab p q hlen ihp ihq =>
        Hint (hidden := true) "When the heads differ and the left branch wins,
        `lcs (a::xs) (b::ys) = lcs (a::xs) ys`, so trans through dropping `b`."
        rw [lcs, if_neg hab, if_pos hlen]; exact ihp.trans (List.sublist_cons_self b ys)
    | case5 a xs b ys hab p q hlen ihp ihq => rw [lcs, if_neg hab, if_neg hlen]; exact ihq

Conclusion "Verified: `lcs` is always a common subsequence of both lists."

NewDefinition Game.Design.lcs Game.Design.lcs.induct
NewTheorem Game.Design.lcs_nil_left Game.Design.lcs_nil_right List.sublist_cons_self
  List.Sublist.cons₂ List.Sublist.trans List.nil_sublist
