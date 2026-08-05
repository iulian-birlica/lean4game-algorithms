import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 1
Title "Computable Closure"
-- source: RequestProject Lab21.Computable_not, Lab21.Computable_and, Lab21.Computable_or

Introduction "A new strand: **computability**. Can a problem be solved by *any* algorithm at
all? `ComputablePred p` says `p` has a genuinely computable decision procedure. Prove the
computable predicates form a Boolean algebra: closed under `¬`, `∧`, and `∨`. (The prototype
undecidable predicate — the **halting problem** — is coming a few levels down this road.)"

Statement {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun a => ¬ p a) ∧
    ComputablePred (fun a => p a ∧ q a) ∧
    ComputablePred (fun a => p a ∨ q a) := by
  Hint "Negation is `ComputablePred.not`. Conjunction/disjunction each destructure both decision
  procedures and glue them with `Computable.cond`, matching `decide (p ∧ q)`/`decide (p ∨ q)` to
  the resulting conditional via `Bool.decide_and`/`Bool.decide_or`."
  refine ⟨hp.not, ?_, ?_⟩
  · obtain ⟨_, hp⟩ := hp
    obtain ⟨_, hq⟩ := hq
    refine ⟨inferInstance, ?_⟩
    convert Computable.cond hp hq (Computable.const false) using 1
    funext a; rw [Bool.decide_and]; cases hp : decide (p a) <;> rfl
  · Hint (hidden := true) "The disjunction case is the mirror image, matching
    `decide (p ∨ q) = bif decide p then true else decide q`."
    obtain ⟨_, hpc⟩ := hp
    obtain ⟨_, hqc⟩ := hq
    use by infer_instance
    convert Computable.cond hpc (Computable.const true) hqc using 1
    funext a; rw [Bool.decide_or]; cases hp : decide (p a) <;> rfl

Conclusion "Verified: computable predicates are closed under negation, conjunction, and
disjunction."

NewDefinition Computable inferInstance
NewTactic infer_instance funext
NewTheorem ComputablePred.not Computable.cond Computable.const Bool.decide_and Bool.decide_or
