import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 3
Title "Syntactic Properties"
-- source: RequestProject Lab21.syntactic_decidable

Introduction "Rice's theorem needs *behaviour*-invariance. A purely **syntactic** property of
the code — one you can read off the datatype without running it — can be perfectly decidable,
and does not contradict Rice, since it is not behaviour-invariant (many codes share
`Code.zero`'s behaviour). Prove the boundary case: 'is `c` literally the code `Code.zero`?' is
decidable."

Statement : ComputablePred (fun c : Nat.Partrec.Code => c = Nat.Partrec.Code.zero) := by
  Hint "`Code` has decidable equality, so the decision procedure exists classically; the
  computability obligation is to build a computable function matching `decide (c = Code.zero)`,
  by cases on `c`'s outermost constructor."
  have h_decidable : DecidablePred (fun c : Nat.Partrec.Code => c = Nat.Partrec.Code.zero) := by
    exact fun c => Classical.propDecidable _
  refine' ⟨h_decidable, _⟩
  convert Computable.of_eq _ _
  exact fun c => match c with | Nat.Partrec.Code.zero => Bool.true | _ => Bool.false
  · Hint (hidden := true) "`Computable.nat_casesOn` on `c`'s encoding distinguishes the `zero`
    constructor (encoded as `0`) from every other case."
    convert Computable.nat_casesOn (Computable.id) _ _
    rotate_left
    exact Bool
    exact inferInstance
    exact fun _ => Bool.true
    exact fun _ _ => Bool.false
    · exact Computable.const Bool.true
    · exact Computable.const false
    · constructor <;> intro h
      · convert Computable.nat_casesOn (Computable.id) _ _ using 1
        · exact Computable.const true
        · exact Computable.const false
      · convert h.comp (Computable.encode) using 1
        ext (_ | _ | _ | _ | _ | _) <;> rfl
  · intro n; cases n <;> simp

Conclusion "Verified: a purely syntactic property can be decidable even though Rice's theorem
rules out every non-trivial *behavioural* one."

NewDefinition Nat.Partrec.Code.zero DecidablePred Classical.propDecidable
NewTactic rotate_left «match»
NewTheorem Computable.of_eq Computable.nat_casesOn Computable.id Computable.encode
