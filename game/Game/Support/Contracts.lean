import Mathlib

/-! Answer-free definitions used by the Contracts world. Ported from the course's
`RequestProject/Lab01HoareTriples.lean` (via the earlier custom-format prototype
in `game/Game/Contracts/`). No level solutions live here. -/
namespace Game.Contracts

/-- A list is sorted iff it is pairwise non-decreasing. -/
def IsSorted (l : List Int) : Prop := List.Pairwise (· ≤ ·) l

/-- The routine under contract: sum every element of the list. -/
def sum (values : List Int) : Int := values.foldr (· + ·) 0

/-- The routine under contract: the greatest common divisor of two naturals. -/
def gcd (a b : Nat) : Nat := Nat.gcd a b

/-- The routine under contract: reverse a list. -/
def reverse {T : Type} (values : List T) : List T := values.reverse

/-- The routine under contract: remove one occurrence of `x` from the list. -/
def removeFirst {T : Type} [DecidableEq T] (values : List T) (x : T) : List T := values.erase x

/-- The routine under contract: sort a list of integers. -/
def sort (values : List Int) : List Int := values.mergeSort (fun a b => decide (a ≤ b))

/-- An array is sorted iff every earlier index holds a value `≤` every later index. -/
def IsSortedArr (a : Array Int) : Prop :=
  ∀ (i j : Nat) (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]

/-- Binary search restricted to the half-open window `[lo, hi)`. -/
def binarySearchAux (a : Array Int) (target : Int) (lo hi : Nat)
    (hhi : hi ≤ a.size) : Bool :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    have hmid : mid < hi := by omega
    have hlt : mid < a.size := by omega
    let v := a[mid]
    if v = target then true
    else if v < target then binarySearchAux a target (mid + 1) hi hhi
    else binarySearchAux a target lo mid (by omega)
  else false
termination_by hi - lo
decreasing_by all_goals omega

/-- The routine under contract: binary search over a sorted array. -/
def binarySearch (a : Array Int) (target : Int) : Bool :=
  binarySearchAux a target 0 a.size (le_refl _)

/-- Supplied "card": on a sorted array, searching the window `[lo, hi)` succeeds
iff `target` occurs at some index inside that window. This is the interval
invariant the `BinarySearch` boss level is allowed to use as a black box. -/
theorem binarySearchAux_spec (a : Array Int) (target : Int) (hsorted : IsSortedArr a)
    (lo hi : Nat) (hhi : hi ≤ a.size) :
    binarySearchAux a target lo hi hhi = true ↔
      ∃ (i : Nat) (h : i < a.size), lo ≤ i ∧ i < hi ∧ a[i] = target := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi
  unfold binarySearchAux
  by_cases h : lo < hi
  · rw [dif_pos h]
    extract_lets mid hmid hlt v
    have hmiddef : mid = (lo + hi) / 2 := rfl
    have hvdef : v = a[mid] := rfl
    have hlomid : lo ≤ mid := by omega
    by_cases hvt : v = target
    · rw [if_pos hvt]
      constructor
      · intro _
        exact ⟨mid, hlt, hlomid, hmid, by rw [← hvdef]; exact hvt⟩
      · intro _; rfl
    · rw [if_neg hvt]
      by_cases hlt2 : v < target
      · rw [if_pos hlt2]
        rw [ih (hi - (mid + 1)) (by omega) (mid + 1) hi hhi rfl]
        constructor
        · rintro ⟨i, hisz, hmi, hih, hai⟩
          exact ⟨i, hisz, by omega, hih, hai⟩
        · rintro ⟨i, hisz, hloi, hih, hai⟩
          refine ⟨i, hisz, ?_, hih, hai⟩
          by_contra hc
          push_neg at hc
          have hile : i ≤ mid := by omega
          have hmono := hsorted i mid hisz hlt hile
          rw [hai, ← hvdef] at hmono
          exact absurd (lt_of_le_of_lt hmono hlt2) (lt_irrefl _)
      · rw [if_neg hlt2]
        rw [ih (mid - lo) (by omega) lo mid (by omega) rfl]
        constructor
        · rintro ⟨i, hisz, hloi, him, hai⟩
          exact ⟨i, hisz, hloi, by omega, hai⟩
        · rintro ⟨i, hisz, hloi, hih, hai⟩
          refine ⟨i, hisz, hloi, ?_, hai⟩
          by_contra hc
          push_neg at hc
          have hmi : mid ≤ i := by omega
          have hmono := hsorted mid i hlt hisz hmi
          rw [hai, ← hvdef] at hmono
          have htv : target < v := lt_of_le_of_ne (not_lt.mp hlt2) (fun hh => hvt hh.symm)
          exact absurd (lt_of_le_of_lt hmono htv) (lt_irrefl _)
  · rw [dif_neg h]
    constructor
    · intro hcon; exact absurd hcon Bool.false_ne_true
    · rintro ⟨i, _, hlo, hih, _⟩; omega

/-! ## Lab 04 — invariants: given definitions and cross-level cards

Ported from `RequestProject/Lab04Invariants.lean`. As with the binary-search
material above, definitions and *given* facts live here; the level files
still perform the invariant/induction proofs the lab teaches. -/

/-- The loop of `suma`: the value of the accumulator after `i` steps. -/
def sumaAux (v : ℕ → Int) : ℕ → Int
  | 0 => 0
  | (i + 1) => sumaAux v i + v i

/-- The routine under contract: sum the first `n` entries of `v`. -/
def suma (v : ℕ → Int) (n : ℕ) : Int := sumaAux v n

/-- One pass of adjacent compare–swaps (the inner `for` loop of bubble sort). -/
def bubblePass : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x ≤ y then x :: bubblePass (y :: rest)
      else y :: bubblePass (x :: rest)

/-- **Given**: a pass does not change the length. Played in the "Bubble
Chamber" level; supplied here (and used by `bubbleSort`'s own termination
proof) so later facts can build on it. -/
theorem bubblePass_length (l : List Int) : (bubblePass l).length = l.length := by
  induction l using bubblePass.induct with
  | case1 => rw [bubblePass]
  | case2 x => rw [bubblePass]
  | case3 x y rest hxy ih => rw [bubblePass, if_pos hxy]; simp only [List.length_cons, ih]
  | case4 x y rest hxy ih => rw [bubblePass, if_neg hxy]; simp only [List.length_cons, ih]

/-- **Given**: a pass only rearranges the elements. Played in the "Bubble
Chamber" level; supplied here for `bubbleSort_perm`. -/
theorem bubblePass_perm (l : List Int) : (bubblePass l).Perm l := by
  induction l using bubblePass.induct with
  | case1 => rw [bubblePass]
  | case2 x => rw [bubblePass]
  | case3 x y rest hxy ih => rw [bubblePass, if_pos hxy]; exact ih.cons x
  | case4 x y rest hxy ih =>
      rw [bubblePass, if_neg hxy]; exact (ih.cons y).trans (List.Perm.swap x y rest)

/-- A pass is nonempty exactly when its input is (it preserves length). -/
theorem bubblePass_ne_nil {l : List Int} (h : l ≠ []) : bubblePass l ≠ [] := by
  intro hcon
  have hlen := bubblePass_length l
  rw [hcon, List.length_nil] at hlen
  exact h (List.length_eq_zero_iff.mp hlen.symm)

/-- **Given**: after one pass the last element is the maximum — the
inner-loop invariant `bubbleSort_sorted` is built from. Out of scope for
the "Bubble Pass Length and Permutation" level itself (which plays `bubblePass_length` and
`bubblePass_perm`), but essential infrastructure for the boss level. -/
theorem bubblePass_getLast_ge (l : List Int) (hne : bubblePass l ≠ []) :
    ∀ x ∈ l, x ≤ (bubblePass l).getLast hne := by
  induction l using bubblePass.induct with
  | case1 => rw [bubblePass] at hne; exact absurd rfl hne
  | case2 x =>
      intro a ha; rw [List.mem_singleton] at ha; subst ha
      simp only [bubblePass, List.getLast_singleton, le_refl]
  | case3 x y rest hxy ih =>
      have hbp : bubblePass (y :: rest) ≠ [] := bubblePass_ne_nil (List.cons_ne_nil y rest)
      have hcons : x :: bubblePass (y :: rest) ≠ [] := List.cons_ne_nil _ _
      have hstep : bubblePass (x :: y :: rest) = x :: bubblePass (y :: rest) := by
        rw [bubblePass, if_pos hxy]
      have hlast : (bubblePass (x :: y :: rest)).getLast hne
          = (bubblePass (y :: rest)).getLast hbp := by
        rw [List.getLast_congr hne hcons hstep, List.getLast_cons hbp]
      have ihy := ih hbp
      intro a ha; rw [hlast]; simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact le_trans hxy (ihy y (List.mem_cons_self ..))
      · exact ihy a (List.mem_cons_self ..)
      · exact ihy a (List.mem_cons_of_mem _ ha)
  | case4 x y rest hxy ih =>
      have hxy' : y ≤ x := le_of_lt (lt_of_not_ge hxy)
      have hbp : bubblePass (x :: rest) ≠ [] := bubblePass_ne_nil (List.cons_ne_nil x rest)
      have hcons : y :: bubblePass (x :: rest) ≠ [] := List.cons_ne_nil _ _
      have hstep : bubblePass (x :: y :: rest) = y :: bubblePass (x :: rest) := by
        rw [bubblePass, if_neg hxy]
      have hlast : (bubblePass (x :: y :: rest)).getLast hne
          = (bubblePass (x :: rest)).getLast hbp := by
        rw [List.getLast_congr hne hcons hstep, List.getLast_cons hbp]
      have ihx := ih hbp
      intro a ha; rw [hlast]; simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact ihx a (List.mem_cons_self ..)
      · exact le_trans hxy' (ihx x (List.mem_cons_self ..))
      · exact ihx a (List.mem_cons_of_mem _ ha)

/-- The recursive sort: bubble one pass, keep the maximal last element
fixed, and sort the remaining prefix. -/
def bubbleSort (l : List Int) : List Int :=
  if h : l.length = 0 then []
  else
    let p := bubblePass l
    have hp : p ≠ [] := by
      have hlen : p.length = l.length := bubblePass_length l
      intro hcon
      rw [hcon] at hlen
      simp only [List.length_nil] at hlen
      omega
    bubbleSort p.dropLast ++ [p.getLast hp]
termination_by l.length
decreasing_by
  simp only [List.length_dropLast, bubblePass_length]
  omega

/-- **Given**: `bubbleSort` returns a permutation of its input — one half of
the "Bubble Sort Correctness" level's assembled contract. -/
theorem bubbleSort_perm (l : List Int) : (bubbleSort l).Perm l := by
  induction l using bubbleSort.induct with
  | case1 x hlen =>
      rw [bubbleSort, dif_pos hlen, List.length_eq_zero_iff.mp hlen]
  | case2 x hlen p hpne ih =>
      rw [bubbleSort, dif_neg hlen]
      refine (List.Perm.append_right _ ih).trans ?_
      rw [List.dropLast_append_getLast hpne]
      exact bubblePass_perm x

/-- **Given**: `bubbleSort` returns a sorted list — the other half of the
"Bubble Sort Correctness" level's assembled contract. -/
theorem bubbleSort_sorted (l : List Int) : List.Pairwise (· ≤ ·) (bubbleSort l) := by
  induction l using bubbleSort.induct with
  | case1 x hlen => rw [bubbleSort, dif_pos hlen]; exact List.Pairwise.nil
  | case2 x hlen p hpne ih =>
      rw [bubbleSort, dif_neg hlen, List.pairwise_append]
      refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      have ha_p : a ∈ p := List.mem_of_mem_dropLast ((bubbleSort_perm p.dropLast).mem_iff.mp ha)
      have ha_x : a ∈ x := (bubblePass_perm x).mem_iff.mp ha_p
      exact bubblePass_getLast_ge x hpne a ha_x

/-- Select the minimum and recurse on the remaining elements. -/
def selectionSort (l : List Int) : List Int :=
  if h : 0 < l.length then
    let m := l.minimum_of_length_pos h
    m :: selectionSort (l.erase m)
  else []
termination_by l.length
decreasing_by
  have hm : l.minimum_of_length_pos h ∈ l := List.minimum_of_length_pos_mem h
  rw [List.length_erase_of_mem hm]
  omega

/-- **Given**: `selectionSort` returns a permutation of its input — one half
of the "Selection Sort Correctness" level's assembled contract. -/
theorem selectionSort_perm (l : List Int) : (selectionSort l).Perm l := by
  induction l using selectionSort.induct with
  | case1 l hpos m ih =>
      rw [selectionSort, dif_pos hpos]
      have hm : l.minimum_of_length_pos hpos ∈ l := List.minimum_of_length_pos_mem hpos
      exact (ih.cons _).trans (List.perm_cons_erase hm).symm
  | case2 l hpos =>
      rw [selectionSort, dif_neg hpos]
      have : l = [] := by rw [← List.length_eq_zero_iff]; omega
      rw [this]

/-- **Given**: `selectionSort` returns a sorted list — the other half of the
"Selection Sort Correctness" level's assembled contract. -/
theorem selectionSort_sorted (l : List Int) : List.Pairwise (· ≤ ·) (selectionSort l) := by
  induction l using selectionSort.induct with
  | case1 l hpos m ih =>
      rw [selectionSort, dif_pos hpos, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro a ha
      have ha_erase : a ∈ l.erase (l.minimum_of_length_pos hpos) :=
        (selectionSort_perm _).subset ha
      exact List.minimum_of_length_pos_le_of_mem (List.mem_of_mem_erase ha_erase) hpos
  | case2 l hpos => rw [selectionSort, dif_neg hpos]; exact List.Pairwise.nil

/-- The loop of `countDigits`: strip one digit per step. -/
def countDigits (x : ℕ) : ℕ :=
  if 0 < x then countDigits (x / 10) + 1 else 0
termination_by x
decreasing_by exact Nat.div_lt_self ‹0 < x› (by norm_num)

/-- Euclid's subtractive gcd. -/
def gcdSub (a b : ℕ) : ℕ :=
  if a = 0 then b
  else if b = 0 then a
  else if a = b then a
  else if b < a then gcdSub (a - b) b
  else gcdSub a (b - a)
termination_by a + b
decreasing_by all_goals omega

/-- The inner loop of `control`: the sum of the base-10 digits of `x`. -/
def digitSum (x : ℕ) : ℕ := (Nat.digits 10 x).sum

/-- The one-step recurrence for `digitSum`: peel off the last digit. -/
theorem digitSum_rec (x : ℕ) (h : 0 < x) : digitSum x = x % 10 + digitSum (x / 10) := by
  unfold digitSum
  rw [Nat.digits_def' (by norm_num : 1 < 10) h, List.sum_cons]

/-- The digit sum never exceeds the number itself. -/
theorem digitSum_le (x : ℕ) : digitSum x ≤ x :=
  Nat.digit_sum_le 10 x

/-- The digit sum of a number `> 9` is strictly smaller (so `control`
halts). -/
theorem digitSum_lt (res : ℕ) (h : 9 < res) : digitSum res < res := by
  have hpos : 0 < res := by omega
  rw [digitSum_rec res hpos]
  have hle : digitSum (res / 10) ≤ res / 10 := digitSum_le _
  have hsplit : res = 10 * (res / 10) + res % 10 := (Nat.div_add_mod res 10).symm
  omega

/-- The digit sum of a positive number is positive. -/
theorem digitSum_pos (res : ℕ) (h : 0 < res) : 0 < digitSum res := by
  induction res using Nat.strong_induction_on with
  | _ res ih =>
    rw [digitSum_rec res h]
    rcases Nat.eq_zero_or_pos (res % 10) with h0 | hpos
    · have hle : 10 ≤ res := Nat.le_of_dvd h (Nat.dvd_of_mod_eq_zero h0)
      have := ih (res / 10) (Nat.div_lt_self h (by norm_num)) (by omega)
      omega
    · omega

/-- The outer loop of `control`: iterate `digitSum` until a single digit
remains (the digital root). -/
def control (res : ℕ) : ℕ :=
  if 9 < res then control (digitSum res) else res
termination_by res
decreasing_by exact digitSum_lt res ‹9 < res›

/-- **Given**: a positive input has a positive digital root — needed inside
the "Digital Root Correctness" level's closed-form derivation, but not itself one
of that level's three played facts. -/
theorem control_pos (n : ℕ) (hn : 0 < n) : 0 < control n := by
  induction n using control.induct with
  | case1 n hn2 ih => rw [control, if_pos hn2]; exact ih (digitSum_pos n hn)
  | case2 n hn2 => rw [control, if_neg hn2]; exact hn

end Game.Contracts
