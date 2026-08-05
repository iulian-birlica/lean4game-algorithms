import Game.Metadata

World "Greedy"
Level 1
Title "Carried Proofs"

Introduction "A proof-carrying value is ordinary data bundled with a proof
about that data. In Lean, `{ m : ℕ // m = n }` means: a natural number `m`,
together with proof that this particular `m` equals `n`.

The data is `cert.1`. The carried proof is `cert.2`."

Statement (n : ℕ) (cert : { m : ℕ // m = n }) :
    cert.1 = n := by
  Hint "The goal is exactly the proof stored inside `cert`."
  Hint (hidden := true) "`exact cert.2`."
  exact cert.2

Conclusion "A certificate is useful because its proof component can solve
goals about the carried value directly."
