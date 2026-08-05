import Game.Metadata

World "ProofAutomation"
Level 1
Title "Aesop Search"
-- source: RequestProject Lab18.and_comm_manual, Lab18.and_comm_aesop, Lab18.distrib_aesop

Introduction "Every proof so far has been transparent: elementary steps, or a `simp only
[named lemmas]` that still names every rule it uses. This world audits three *search*
tactics deliberately held back until now. First, `aesop` ('Automated Extensible Search for
Obvious Proofs') runs a best-first search over intro/elimination rules and simp lemmas — the
natural finisher for goals that are 'obvious' by a short combination of logical steps.
Compare the hand proof `exact ⟨h.2, h.1⟩` of `p ∧ q → q ∧ p` with letting `aesop` find it
(you've already met `aesop` once, in Design); now put it to work on a compound
propositional goal."

Statement (p q r : Prop) : (p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r)) := by
  Hint "This is exactly the intro/case-split/elimination search `aesop` automates — a hand
  proof would spell it out with `rintro`/`rcases`/`exact`."
  aesop

Conclusion "Audited: `aesop` finds the same short logical proofs a hand-written
`rintro`/`rcases`/`exact` script would, for goals built from intro/elimination rules alone."
