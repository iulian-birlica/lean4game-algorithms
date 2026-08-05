import Mathlib

namespace Game.Clockwork

/-- One stable pass of least-significant-digit radix sort in base two: keep the
elements whose bit `i` is `0` (in their original order), followed by those whose
bit `i` is `1` (in their original order). This is a *non-comparison* step — it
never compares two elements, it only inspects a single bit of each. -/
def bitPass (i : ℕ) (l : List ℕ) : List ℕ :=
  l.filter (fun x => x / 2 ^ i % 2 == 0) ++ l.filter (fun x => x / 2 ^ i % 2 != 0)

/-- Binary LSD radix sort: apply `bitPass` for bit `0`, then bit `1`, up to bit
`n - 1`. After `n` passes the list is sorted by its low `n` bits, so if every
element is below `2 ^ n` the result is fully sorted. -/
def binaryRadixSort : ℕ → List ℕ → List ℕ
  | 0, l => l
  | (k + 1), l => bitPass k (binaryRadixSort k l)

end Game.Clockwork
