import Mathlib

namespace Game.Clockwork

/-- One step of selection: scan the list carrying the current candidate minimum
`x`, and return the overall minimum together with the remaining elements (in
their original relative order). This is the first of the two functions of the
classic functional selection sort. -/
def select (x : ℕ) : List ℕ → ℕ × List ℕ
  | [] => (x, [])
  | y :: ys =>
    if x ≤ y then
      let p := select x ys
      (p.1, y :: p.2)
    else
      let p := select y ys
      (p.1, x :: p.2)

/-- Selection leaves behind exactly the elements it did not pick, so the leftover
list has the same length as the input. This fact is what makes the recursion in
`selectionSort` terminate. -/
theorem select_length (x : ℕ) (l : List ℕ) : (select x l).2.length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih => simp only [select]; split <;> simp [ih]

/-- Functional selection sort, the second of the two functions: repeatedly pull
out the minimum with `select` and recurse on the remaining elements. -/
def selectionSort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let p := select x xs
    p.1 :: selectionSort p.2
  termination_by l => l.length
  decreasing_by simp_wf; have := select_length x xs; omega

end Game.Clockwork
