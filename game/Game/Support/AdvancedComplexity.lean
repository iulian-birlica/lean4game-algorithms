import Game.Support.Complexity

namespace Game.AdvancedComplexity

open Game.Complexity

/-- A signed literal over an arbitrary variable type. -/
structure SignedLiteral (α : Type) where
  name : α
  positive : Bool
  deriving DecidableEq

namespace SignedLiteral

/-- Evaluate a signed literal under a Boolean assignment. -/
def eval {α : Type} (assignment : α → Bool) (literal : SignedLiteral α) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

/-- The positive literal on `name`. -/
def pos {α : Type} (name : α) : SignedLiteral α := ⟨name, true⟩

/-- The negative literal on `name`. -/
def neg {α : Type} (name : α) : SignedLiteral α := ⟨name, false⟩

end SignedLiteral

/-- Three signed literals over variables of type `α`. -/
abbrev GenericClause3 (α : Type) := SignedLiteral α × SignedLiteral α × SignedLiteral α

/-- A 3-CNF formula over variables of type `α`. -/
abbrev GenericCNF3 (α : Type) := List (GenericClause3 α)

/-- Evaluate a three-literal clause. -/
def evalGenericClause3 {α : Type} (assignment : α → Bool) (clause : GenericClause3 α) : Bool :=
  clause.1.eval assignment || clause.2.1.eval assignment || clause.2.2.eval assignment

/-- Evaluate a conjunction of three-literal clauses. -/
def evalGenericCNF3 {α : Type} (assignment : α → Bool) (formula : GenericCNF3 α) : Bool :=
  formula.all (evalGenericClause3 assignment)

/-- Satisfiability for the generic 3-CNF model. -/
def GenericSatisfiable3 {α : Type} (formula : GenericCNF3 α) : Prop :=
  ∃ assignment : α → Bool, evalGenericCNF3 assignment formula = true

/-- Tseitin variables include the original atoms and one auxiliary name for
each subformula. -/
abbrev TseitinVariable := Sum Nat Formula

namespace Tseitin

open SignedLiteral

/-- The auxiliary variable naming a subformula. -/
def aux (formula : Formula) : TseitinVariable := Sum.inr formula

/-- The variable corresponding to an original atom. -/
def atom (name : Nat) : TseitinVariable := Sum.inl name

/-- Package three signed literals into a clause. -/
def clause (a b c : SignedLiteral TseitinVariable) : GenericClause3 TseitinVariable :=
  (a, b, c)

/-- Gate clauses forcing each auxiliary variable to equal its subformula's
semantic value. Short clauses are padded by repeating literals. -/
def gates : Formula → GenericCNF3 TseitinVariable
  | f@(.atom name) =>
      [clause (neg (aux f)) (pos (atom name)) (pos (atom name)),
       clause (pos (aux f)) (neg (atom name)) (neg (atom name))]
  | f@.falsum =>
      [clause (neg (aux f)) (neg (aux f)) (neg (aux f))]
  | f@(.neg body) =>
      clause (neg (aux f)) (neg (aux body)) (neg (aux body)) ::
      clause (pos (aux f)) (pos (aux body)) (pos (aux body)) ::
      gates body
  | f@(.conj left right) =>
      clause (neg (aux f)) (pos (aux left)) (pos (aux left)) ::
      clause (neg (aux f)) (pos (aux right)) (pos (aux right)) ::
      clause (pos (aux f)) (neg (aux left)) (neg (aux right)) ::
      (gates left ++ gates right)
  | f@(.disj left right) =>
      clause (pos (aux f)) (neg (aux left)) (neg (aux left)) ::
      clause (pos (aux f)) (neg (aux right)) (neg (aux right)) ::
      clause (neg (aux f)) (pos (aux left)) (pos (aux right)) ::
      (gates left ++ gates right)

/-- The complete Tseitin transformation asserts the root variable too. -/
def transform (formula : Formula) : GenericCNF3 TseitinVariable :=
  clause (pos (aux formula)) (pos (aux formula)) (pos (aux formula)) :: gates formula

/-- Extend an atom assignment to all auxiliary variables by semantic
evaluation. -/
def canonicalAssignment (assignment : Nat → Bool) : TseitinVariable → Bool
  | Sum.inl name => assignment name
  | Sum.inr formula => formula.eval assignment

/-- Count nodes in a formula syntax tree. -/
def nodeCount : Formula → Nat
  | .atom _ | .falsum => 1
  | .neg body => nodeCount body + 1
  | .conj left right | .disj left right => nodeCount left + nodeCount right + 1

end Tseitin

/-- SAT measured by formula syntax-tree size. -/
def formulaSATProblem : DecisionProblem where
  Input := Formula
  size := Tseitin.nodeCount
  pred := Formula.Satisfiable

/-- The concrete 3SAT target produced by the Tseitin transform. -/
def tseitin3SATProblem : DecisionProblem where
  Input := GenericCNF3 TseitinVariable
  size := List.length
  pred := GenericSatisfiable3

/-- A package of named Hamiltonian reductions and NP-membership facts. -/
structure HamiltonianReductionCards where
  pathProblem : DecisionProblem
  cycleProblem : DecisionProblem
  satToPath : Reduces formulaSATProblem pathProblem
  pathToCycle : Reduces pathProblem cycleProblem
  cycleToPath : Reduces cycleProblem pathProblem
  path_inNP : inNP pathProblem
  cycle_inNP : inNP cycleProblem

/-- A concrete machine model with deterministic and nondeterministic step
relations. -/
structure SpaceMachine (Input : Type) where
  Config : Type
  start : Input → Config
  accept : Config → Prop
  space : Config → Nat
  next : Config → Option Config
  step : Config → Config → Prop

namespace SpaceMachine

/-- The step relation induced by the deterministic successor function. -/
def deterministicStep {Input : Type} (machine : SpaceMachine Input)
    (c d : machine.Config) : Prop :=
  machine.next c = some d

/-- Acceptance by a deterministic run. -/
def deterministicAccepts {Input : Type} (machine : SpaceMachine Input) (input : Input) : Prop :=
  ∃ final, Relation.ReflTransGen machine.deterministicStep (machine.start input) final ∧
    machine.accept final

/-- Acceptance by a nondeterministic run. -/
def nondeterministicAccepts {Input : Type} (machine : SpaceMachine Input) (input : Input) : Prop :=
  ∃ final, Relation.ReflTransGen machine.step (machine.start input) final ∧
    machine.accept final

/-- Every deterministic transition is also a nondeterministic one. -/
def DeterministicIncluded {Input : Type} (machine : SpaceMachine Input) : Prop :=
  ∀ c d, machine.deterministicStep c d → machine.step c d

end SpaceMachine

end Game.AdvancedComplexity
