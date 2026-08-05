import Game.Metadata
import Game.Support.RadixSort
import Game.Levels.RadixSort.L02_RadixSortPerm

open Game.Clockwork

World "RadixSort"
Level 3
Title "One Pass Refines the Ordering"

Introduction "Here is the heart of radix-sort correctness. Sort a list by its low
`i` bits — that is, by the key `a % 2 ^ i` — and then run one more pass on bit
`i`. The result is sorted by the low `i + 1` bits. The zero-bit block keeps its
order and stays below `2 ^ i`; the one-bit block keeps its order and sits at or
above `2 ^ i`; so the two blocks are ordered correctly relative to each other.
The key identity is `Nat.mod_pow_succ`:
`a % 2 ^ (i+1) = a % 2 ^ i + 2 ^ i * (a / 2 ^ i % 2)`."

/-- One bit pass turns a list sorted by its low `i` bits into one sorted by its
low `i + 1` bits. -/
Statement bitPass_pairwise_step (i : ℕ) (s : List ℕ)
    (h : s.Pairwise (fun a b => a % 2 ^ i ≤ b % 2 ^ i)) :
    (bitPass i s).Pairwise (fun a b => a % 2 ^ (i + 1) ≤ b % 2 ^ (i + 1)) := by
  Hint "Unfold `bitPass` and use `List.pairwise_append`. Each filtered block is
  `Pairwise` by `List.Pairwise.filter`; upgrade the key with
  `List.Pairwise.imp_of_mem` and `Nat.mod_pow_succ`. For the cross condition, a
  zero-bit key is `< 2 ^ i` while a one-bit key is `≥ 2 ^ i`."
  unfold bitPass
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · have hz : (s.filter (fun x => x / 2 ^ i % 2 == 0)).Pairwise
        (fun a b => a % 2 ^ i ≤ b % 2 ^ i) := h.filter _
    refine hz.imp_of_mem ?_
    intro a b ha hb hab
    rw [List.mem_filter] at ha hb
    have ha0 : a / 2 ^ i % 2 = 0 := by simpa using ha.2
    have hb0 : b / 2 ^ i % 2 = 0 := by simpa using hb.2
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ha0, hb0]
    simpa using hab
  · have ho : (s.filter (fun x => x / 2 ^ i % 2 != 0)).Pairwise
        (fun a b => a % 2 ^ i ≤ b % 2 ^ i) := h.filter _
    refine ho.imp_of_mem ?_
    intro a b ha hb hab
    rw [List.mem_filter] at ha hb
    have ha1 : a / 2 ^ i % 2 = 1 := by
      have := ha.2; simp only [bne_iff_ne, ne_eq] at this; omega
    have hb1 : b / 2 ^ i % 2 = 1 := by
      have := hb.2; simp only [bne_iff_ne, ne_eq] at this; omega
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ha1, hb1]
    simpa using hab
  · intro a ha b hb
    rw [List.mem_filter] at ha hb
    have ha0 : a / 2 ^ i % 2 = 0 := by simpa using ha.2
    have hb1 : b / 2 ^ i % 2 = 1 := by
      have := hb.2; simp only [bne_iff_ne, ne_eq] at this; omega
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ha0, hb1]
    have : a % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
    simp only [mul_zero, add_zero, mul_one]
    omega

Conclusion "Each pass adds exactly one more bit of order — the invariant that
makes radix sort work."

NewTactic unfold rw refine intro simpa simp omega positivity exact
NewTheorem List.pairwise_append List.Pairwise.filter List.Pairwise.imp_of_mem
  List.mem_filter Nat.mod_pow_succ Nat.mod_lt bitPass_pairwise_step
