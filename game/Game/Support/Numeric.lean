import Mathlib

/-! Answer-free definitions used by the numeric-algorithms world. Ported from
the older game tree and adapted to the current project layout. -/
namespace Game.Numeric

/-- Repeated squaring with an accumulator. Each recursive call removes the low
binary digit of the exponent. -/
def binaryPowAux (base exponent accumulator : Nat) : Nat :=
  if exponent = 0 then accumulator
  else
    binaryPowAux (base * base) (exponent / 2)
      (if exponent % 2 = 1 then accumulator * base else accumulator)
termination_by exponent
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹exponent ≠ 0›) (by omega)

/-- Fast exponentiation, started from accumulator `1`. -/
def binaryPow (base exponent : Nat) : Nat :=
  binaryPowAux base exponent 1

/-- Number of binary digits processed by repeated squaring. -/
def powSteps : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + powSteps ((n + 1) / 2)
termination_by n => n
decreasing_by omega

/-- Number of remainder operations performed by Euclid's algorithm. -/
def euclidSteps (a b : Nat) : Nat :=
  if b = 0 then 0 else 1 + euclidSteps b (a % b)
termination_by b
decreasing_by
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

/-- Repeated-squaring modular exponentiation. -/
def modularPowAux (modulus base exponent accumulator : Nat) : Nat :=
  if exponent = 0 then accumulator % modulus
  else
    modularPowAux modulus ((base * base) % modulus) (exponent / 2)
      (if exponent % 2 = 1 then (accumulator * base) % modulus else accumulator % modulus)
termination_by exponent
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹exponent ≠ 0›) (by omega)

/-- Modular exponentiation started from accumulator `1`. -/
def modularPow (modulus base exponent : Nat) : Nat :=
  modularPowAux modulus base exponent 1

/-- Remove the positive multiples of `p` from a finite candidate set. -/
def crossOut (p : Nat) (candidates : Finset Nat) : Finset Nat :=
  candidates.filter fun n => ¬p ∣ n

/-- The mathematical result computed by a sieve up to `bound`. -/
def sieveCandidates (bound : Nat) : Finset Nat :=
  (Finset.range (bound + 1)).filter Nat.Prime

/-- Candidate proper divisors tested by elementary trial division. -/
def trialDivisors (n : Nat) : Finset Nat :=
  (Finset.range n).filter fun d => 2 ≤ d ∧ d ∣ n

/-- Trial-division primality testing, expressed through absence of nontrivial
proper divisors. -/
def trialPrime (n : Nat) : Bool :=
  decide (2 ≤ n ∧ trialDivisors n = ∅)

end Game.Numeric
