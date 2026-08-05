import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 7
Title "Busy Beaver Has No Computable Bound"
-- source: RequestProject Lab22.busy_beaver_principle, Lab22.bbSteps_not_computable

Introduction "The reduction that ends the course: if some **computable** function bounded
every program's halting time, you could decide halting itself — just run the program that
many steps and check whether it stopped. Since halting is undecidable, no such computable
bound exists (the **Busy Beaver principle**). Hence `bbSteps` — a perfectly well-defined
function, a maximum over a finite set of programs — cannot itself be computable."

Statement :
    (¬ ∃ f : ℕ → ℕ, Computable f ∧
      ∀ c : Nat.Partrec.Code, (c.eval 0).Dom →
        (Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0).isSome) ∧
    ¬ Computable bbSteps := by
  Hint "The principle: from a hypothetical computable bound `f`, build the decision procedure
  'run `c` for `f (code c)` steps and test success' — it agrees with genuine halting by
  soundness (⇐) and the assumed bound (⇒), contradicting `halting_on_zero_undecidable`.
  Uncomputability of `bbSteps` then follows at once: `bbSteps` itself would be such a bound, by
  the two previous levels' facts."
  have hprinciple : ¬ ∃ f : ℕ → ℕ, Computable f ∧
      ∀ c : Nat.Partrec.Code, (c.eval 0).Dom →
        (Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0).isSome := by
    rintro ⟨f, hf, hbound⟩
    apply halting_on_zero_undecidable
    have hg : Computable (fun c : Nat.Partrec.Code =>
        (Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0).isSome) := by
      have h1 : Computable (fun c : Nat.Partrec.Code => f (Encodable.encode c)) :=
        hf.comp Computable.encode
      have h3 : Computable (fun c : Nat.Partrec.Code =>
          Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0) :=
        (Nat.Partrec.Code.primrec_evaln.to_comp).comp
          ((h1.pair Computable.id).pair (Computable.const 0))
      exact Primrec.option_isSome.to_comp.comp h3
    refine ComputablePred.computable_iff.2 ⟨_, hg, funext fun c => propext ?_⟩
    exact ⟨fun hdom => hbound c hdom, fun hs => by
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
      exact Part.dom_iff_mem.2 ⟨x, Nat.Partrec.Code.evaln_sound (by rw [hx]; rfl)⟩⟩
  refine ⟨hprinciple, ?_⟩
  Hint (hidden := true) "Assume `bbSteps` computable; combine `haltTime_spec` and
  `evaln_isSome_mono` with the previous level's `haltTime_le_bbSteps` to show it would satisfy
  the principle's bound, contradicting `hprinciple`."
  intro h
  exact hprinciple ⟨bbSteps, h,
    fun c hdom => evaln_isSome_mono (haltTime_spec hdom) (haltTime_le_bbSteps c)⟩

Conclusion "Verified: the Busy Beaver step function — well-defined, and unavoidable in any
theory of computation — is provably uncomputable. It in fact dominates every computable
function (an optional further exercise, `bbSteps_dominates`, left as a bonus). Course complete."

NewTheorem Game.Complexity.halting_on_zero_undecidable Game.Complexity.haltTime_spec
  Game.Complexity.evaln_isSome_mono Game.Complexity.haltTime_le_bbSteps
  Nat.Partrec.Code.primrec_evaln Nat.Partrec.Code.evaln_sound Computable.pair
  ComputablePred.computable_iff Primrec.option_isSome propext
