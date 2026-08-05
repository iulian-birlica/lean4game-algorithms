import Game.Metadata
import Game.Levels.Greedy.L01_CarriedProofs

World "Greedy"
Level 2
Title "Carried Rewrite"

Introduction "Sometimes the certificate carries an equality for a value that
appears inside a larger expression. Then use the carried proof as a rewrite.

Here `cert.2` says that the carried list `cert.1` is exactly `xs`."

Statement (xs : List ℕ)
    (cert : { ys : List ℕ // ys = xs }) :
    cert.1.length = xs.length := by
  Hint "Rewrite with the equality stored in `cert.2`."
  Hint (hidden := true) "`rw [cert.2]`."
  rw [cert.2]

Conclusion "A carried equality can rewrite every occurrence of the certified
value, not just solve an equality goal directly."

NewTactic rw
