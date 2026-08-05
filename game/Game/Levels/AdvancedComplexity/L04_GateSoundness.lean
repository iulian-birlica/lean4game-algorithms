import Game.Metadata
import Game.Support.AdvancedComplexity

open Game.Complexity
open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 4
Title "Tseitin Gate Soundness"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L04GateSoundness.lean

Introduction "Completeness went one way; now go back. Any assignment that
satisfies the local gates must give each auxiliary variable the same truth
value as the subformula it represents."

Statement tseitin_gate_soundness (f : Formula) (a : TseitinVariable → Bool) :
    evalGenericCNF3 a (Tseitin.gates f) = true →
      a (Tseitin.aux f) = Formula.eval (fun n => a (Tseitin.atom n)) f := by
  Hint "Induct on `f`. In the recursive cases, peel off the gate prefix with
  `simp` to recover the hypotheses for the subformulas."
  intro hgates
  induction f with
  | atom name =>
      simp [Tseitin.gates, Tseitin.aux, Tseitin.atom, Tseitin.clause,
        evalGenericCNF3, evalGenericClause3, SignedLiteral.eval,
        SignedLiteral.pos, SignedLiteral.neg, Formula.eval] at hgates ⊢
      aesop
  | falsum =>
      simpa [Tseitin.gates, Tseitin.aux, Tseitin.clause, evalGenericCNF3,
        evalGenericClause3, SignedLiteral.eval, SignedLiteral.neg,
        Formula.eval] using hgates
  | neg body ih =>
      simp [Tseitin.gates, evalGenericCNF3] at hgates
      have hbody : evalGenericCNF3 a (Tseitin.gates body) = true := by
        simpa [evalGenericCNF3] using hgates.2.2
      have hbodyEval := ih hbody
      have hnegGate : a (Tseitin.aux (.neg body)) = false ∨ a (Tseitin.aux body) = false := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg] using hgates.1
      have hposGate : a (Tseitin.aux (.neg body)) = true ∨ a (Tseitin.aux body) = true := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg] using hgates.2.1
      cases hEval : Formula.eval (fun n => a (Tseitin.atom n)) body with
      | false =>
          have hauxBody : a (Tseitin.aux body) = false := by
            simpa [hEval] using hbodyEval
          have hroot : a (Tseitin.aux (.neg body)) = true := by
            rcases hposGate with hroot | hbodyTrue
            · exact hroot
            · have : False := by simpa [hauxBody] using hbodyTrue
              exact False.elim this
          simpa [Formula.eval, hEval] using hroot
      | true =>
          have hauxBody : a (Tseitin.aux body) = true := by
            simpa [hEval] using hbodyEval
          have hroot : a (Tseitin.aux (.neg body)) = false := by
            rcases hnegGate with hroot | hbodyFalse
            · exact hroot
            · have : False := by simpa [hauxBody] using hbodyFalse
              exact False.elim this
          simpa [Formula.eval, hEval] using hroot
  | conj left right ihLeft ihRight =>
      simp [Tseitin.gates, evalGenericCNF3] at hgates
      have hleft : evalGenericCNF3 a (Tseitin.gates left) = true := by
        simpa [evalGenericCNF3] using hgates.2.2.2.1
      have hright : evalGenericCNF3 a (Tseitin.gates right) = true := by
        simpa [evalGenericCNF3] using hgates.2.2.2.2
      have hleftSound := ihLeft hleft
      have hrightSound := ihRight hright
      have hleftGate : a (Tseitin.aux (.conj left right)) = false ∨ a (Tseitin.aux left) = true := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg] using hgates.1
      have hrightGate : a (Tseitin.aux (.conj left right)) = false ∨ a (Tseitin.aux right) = true := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg] using hgates.2.1
      have hrootGate :
          a (Tseitin.aux (.conj left right)) = true ∨
            a (Tseitin.aux left) = false ∨
            a (Tseitin.aux right) = false := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg, or_assoc] using hgates.2.2.1
      cases hLeftEval : Formula.eval (fun n => a (Tseitin.atom n)) left with
      | false =>
          have hleftAux : a (Tseitin.aux left) = false := by
            simpa [hLeftEval] using hleftSound
          cases hRightEval : Formula.eval (fun n => a (Tseitin.atom n)) right with
          | false =>
              have hroot : a (Tseitin.aux (.conj left right)) = false := by
                rcases hleftGate with hroot | hleftTrue
                · exact hroot
                · have : False := by simpa [hleftAux] using hleftTrue
                  exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
          | true =>
              have hroot : a (Tseitin.aux (.conj left right)) = false := by
                rcases hleftGate with hroot | hleftTrue
                · exact hroot
                · have : False := by simpa [hleftAux] using hleftTrue
                  exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
      | true =>
          have hleftAux : a (Tseitin.aux left) = true := by
            simpa [hLeftEval] using hleftSound
          cases hRightEval : Formula.eval (fun n => a (Tseitin.atom n)) right with
          | false =>
              have hrightAux : a (Tseitin.aux right) = false := by
                simpa [hRightEval] using hrightSound
              have hroot : a (Tseitin.aux (.conj left right)) = false := by
                rcases hrightGate with hroot | hrightTrue
                · exact hroot
                · have : False := by simpa [hrightAux] using hrightTrue
                  exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
          | true =>
              have hrightAux : a (Tseitin.aux right) = true := by
                simpa [hRightEval] using hrightSound
              have hroot : a (Tseitin.aux (.conj left right)) = true := by
                rcases hrootGate with hroot | hrest
                · exact hroot
                · rcases hrest with hleftFalse | hrightFalse
                  · have : False := by simpa [hleftAux] using hleftFalse
                    exact False.elim this
                  · have : False := by simpa [hrightAux] using hrightFalse
                    exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
  | disj left right ihLeft ihRight =>
      simp [Tseitin.gates, evalGenericCNF3] at hgates
      have hleft : evalGenericCNF3 a (Tseitin.gates left) = true := by
        simpa [evalGenericCNF3] using hgates.2.2.2.1
      have hright : evalGenericCNF3 a (Tseitin.gates right) = true := by
        simpa [evalGenericCNF3] using hgates.2.2.2.2
      have hleftSound := ihLeft hleft
      have hrightSound := ihRight hright
      have hleftGate : a (Tseitin.aux (.disj left right)) = true ∨ a (Tseitin.aux left) = false := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg] using hgates.1
      have hrightGate : a (Tseitin.aux (.disj left right)) = true ∨ a (Tseitin.aux right) = false := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg] using hgates.2.1
      have hrootGate :
          a (Tseitin.aux (.disj left right)) = false ∨
            a (Tseitin.aux left) = true ∨
            a (Tseitin.aux right) = true := by
        simpa [Tseitin.clause, evalGenericClause3, SignedLiteral.eval,
          SignedLiteral.pos, SignedLiteral.neg, or_assoc] using hgates.2.2.1
      cases hLeftEval : Formula.eval (fun n => a (Tseitin.atom n)) left with
      | false =>
          have hleftAux : a (Tseitin.aux left) = false := by
            simpa [hLeftEval] using hleftSound
          cases hRightEval : Formula.eval (fun n => a (Tseitin.atom n)) right with
          | false =>
              have hrightAux : a (Tseitin.aux right) = false := by
                simpa [hRightEval] using hrightSound
              have hroot : a (Tseitin.aux (.disj left right)) = false := by
                rcases hrootGate with hroot | hrest
                · exact hroot
                · rcases hrest with hleftTrue | hrightTrue
                  · have : False := by simpa [hleftAux] using hleftTrue
                    exact False.elim this
                  · have : False := by simpa [hrightAux] using hrightTrue
                    exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
          | true =>
              have hrightAux : a (Tseitin.aux right) = true := by
                simpa [hRightEval] using hrightSound
              have hroot : a (Tseitin.aux (.disj left right)) = true := by
                rcases hrightGate with hroot | hrightFalse
                · exact hroot
                · have : False := by simpa [hrightAux] using hrightFalse
                  exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
      | true =>
          have hleftAux : a (Tseitin.aux left) = true := by
            simpa [hLeftEval] using hleftSound
          cases hRightEval : Formula.eval (fun n => a (Tseitin.atom n)) right with
          | false =>
              have hroot : a (Tseitin.aux (.disj left right)) = true := by
                rcases hleftGate with hroot | hleftFalse
                · exact hroot
                · have : False := by simpa [hleftAux] using hleftFalse
                  exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot
          | true =>
              have hroot : a (Tseitin.aux (.disj left right)) = true := by
                rcases hleftGate with hroot | hleftFalse
                · exact hroot
                · have : False := by simpa [hleftAux] using hleftFalse
                  exact False.elim this
              simpa [Formula.eval, hLeftEval, hRightEval] using hroot

Conclusion "The gate clauses force every auxiliary variable to mean what it
claims to mean."
