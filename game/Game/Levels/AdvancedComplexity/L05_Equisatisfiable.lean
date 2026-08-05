import Game.Metadata
import Game.Support.AdvancedComplexity
import Game.Levels.AdvancedComplexity.L03_TransformForward
import Game.Levels.AdvancedComplexity.L04_GateSoundness

open Game.Complexity
open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 5
Title "SAT-to-3SAT Equisatisfiability"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L05Equisatisfiable.lean

Introduction "Put the two directions together: the Tseitin transformation does
not change whether a formula is satisfiable."

Statement tseitin_equisatisfiable (f : Formula) :
    Formula.Satisfiable f ↔ GenericSatisfiable3 (Tseitin.transform f) := by
  Hint "For the reverse direction, use the root clause of `Tseitin.transform`
  together with the soundness result from the previous level."
  constructor
  · exact tseitin_transform_forward f
  · rintro ⟨a, ha⟩
    have hsound :
        a (Tseitin.aux f) = Formula.eval (fun n => a (Tseitin.atom n)) f := by
      apply tseitin_gate_soundness
      unfold Tseitin.transform at ha
      simp_all +decide [evalGenericCNF3]
    unfold Tseitin.transform at ha
    simp_all +decide [evalGenericCNF3]
    unfold evalGenericClause3 at ha
    simp_all +decide [Tseitin.clause, SignedLiteral.eval]
    exact ⟨fun n => a (Tseitin.atom n), hsound.symm ▸ ha.1⟩

Conclusion "The SAT instance and its 3SAT encoding succeed or fail together."
