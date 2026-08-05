import Mathlib
import Game.Support.TimeM

/-! Answer-free definitions and given (already-proven) facts used by the
Clockwork world. Ported from `RequestProject/Lab11AsymptoticAnalysis.lean`.
Only the material needed by CAMPAIGN.md's World 3 rows is ported — Lab 11's
Mathlib-asymptotics bridge, the growth-hierarchy theorems (`rpol_isBigO_rpol`,
`rlog_isLittleO_rpol`, …) and the Akra–Bazzi wrapper are not needed by any
played or given level here, so they are omitted rather than carried as dead
code. As elsewhere, theorems here are either prerequisites a level's proof is
allowed to cite, or genuinely out-of-scope infrastructure — the level files
still perform the calculus/assembly proof the lab teaches. No level solutions
live here. -/
namespace Game.Clockwork

open scoped BigOperators
open Cslib.Algorithms.Lean

/-! ## Lab 11 — Landau notation and the Master Theorem -/

/-- `f` is `O(g)` ("big-O"): eventually, `|f|` is bounded by a constant multiple of `|g|`. -/
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ C * |g n|

/-- `f` is `Ω(g)` ("big-Omega"): `f` grows no slower than `g`, i.e. `g = O(f)`. -/
def IsBigOmega (f g : ℕ → ℝ) : Prop := IsBigO g f

/-- `f` is `Θ(g)` ("big-Theta"): `f` and `g` grow at the same rate. -/
def IsBigTheta (f g : ℕ → ℝ) : Prop := IsBigO f g ∧ IsBigO g f

/-- `f` is `o(g)` ("little-o"): `f` grows strictly slower than `g`. -/
def IsLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * |g n|

/-- `f` is `ω(g)` ("little-omega"): `f` grows strictly faster than `g`, i.e. `g = o(f)`. -/
def IsLittleOmega (f g : ℕ → ℝ) : Prop := IsLittleO g f

@[inherit_doc] scoped infix:50 " =O " => IsBigO
@[inherit_doc] scoped infix:50 " =Ω " => IsBigOmega
@[inherit_doc] scoped infix:50 " =Θ " => IsBigTheta
@[inherit_doc] scoped infix:50 " =o " => IsLittleO
@[inherit_doc] scoped infix:50 " =ω " => IsLittleOmega

/-- **Given**: big-O is transitive. Played (re-derived) in the "Big-O
Calculus" level; supplied here so `IsBigTheta.trans` can cite it. -/
theorem IsBigO.trans {f g h : ℕ → ℝ} (hfg : f =O g) (hgh : g =O h) : f =O h := by
  obtain ⟨ C₁, hC₁, N₁, hN₁ ⟩ := hfg;
  obtain ⟨ C₂, hC₂, N₂, hN₂ ⟩ := hgh; exact ⟨ C₁ * C₂, mul_pos hC₁ hC₂, N₁ ⊔ N₂, fun n hn => by simpa only [ mul_assoc, abs_mul ] using le_trans ( hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ) ( mul_le_mul_of_nonneg_left ( hN₂ n ( le_trans ( le_max_right _ _ ) hn ) ) hC₁.le ) ⟩ ;

/-- The reference power function `n ↦ n^s` (real exponent). -/
noncomputable def rpol (s : ℝ) : ℕ → ℝ := fun n => (n : ℝ) ^ s

/-- The reference exponential function `n ↦ e^n`. -/
noncomputable def rexp : ℕ → ℝ := fun n => Real.exp n

/-- The divide-and-conquer cost sequence `Tₖ = T(bᵏ)`: `T₀ = d`, `T_{k+1} = a·Tₖ + F_{k+1}`. -/
def masterSeq (a d : ℝ) (F : ℕ → ℝ) : ℕ → ℝ
  | 0 => d
  | (k + 1) => a * masterSeq a d F k + F (k + 1)

/-- **Given**: closed form of the recurrence. Played (re-derived) in the
"Recurrence Unrolling" level; supplied here so `masterSeq_case1`/
`masterSeq_case2` can cite it. -/
theorem masterSeq_closed (a d : ℝ) (F : ℕ → ℝ) (k : ℕ) :
    masterSeq a d F k = a ^ k * d + ∑ i ∈ Finset.range k, a ^ i * F (k - i) := by
      induction' k with k ih;
      · norm_num [ masterSeq ];
      · rw [ Finset.sum_range_succ', masterSeq ];
        simp_all +decide only [mul_add, Finset.mul_sum _ _ _, add_assoc, pow_succ', mul_assoc, Nat.reduceSubDiff, pow_zero, tsub_zero, one_mul]

/-- **Given**: a reversed geometric sum, with the same constant bound as the
usual geometric partial sum. Needed by `masterSeq_case1_sum_upper`. -/
theorem sum_geom_reverse_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, c ^ (k - i) ≤ (1 - c)⁻¹ := by
  have h_geom_sum : ∑ i ∈ Finset.range k, c ^ (k - i) = ∑ j ∈ Finset.range k, c ^ (j + 1) := by
    rw [ ← Finset.sum_range_reflect ];
    exact Finset.sum_congr rfl fun x hx => by rw [ tsub_tsub, tsub_tsub_cancel_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ] ; ring;
  simp_all +decide [ pow_succ', ← Finset.mul_sum _ _ _ ];
  nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 - c ) ≠ 0 ), pow_nonneg hc0 k, geom_sum_mul c k ]

/-- **Given**: the nonrecursive work in Case 1 contributes only a constant
multiple of `aᵏ`. Needed by `masterSeq_case1`. -/
theorem masterSeq_case1_sum_upper {a M c : ℝ} (ha : 1 ≤ a) (hM : 0 < M)
    (hc0 : 0 ≤ c) (hc1 : c < 1) {F : ℕ → ℝ}
    (hbound : ∀ k, 1 ≤ k → F k ≤ M * a ^ k * c ^ k) (k : ℕ) :
    ∑ i ∈ Finset.range k, a ^ i * F (k - i) ≤ M * a ^ k * (1 - c)⁻¹ := by
  refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( show F ( k - i ) ≤ M * a ^ ( k - i ) * c ^ ( k - i ) from _ ) ( by positivity ) ) _;
  · exact hbound _ ( Nat.sub_pos_of_lt ( Finset.mem_range.mp hi ) );
  · convert mul_le_mul_of_nonneg_left ( sum_geom_reverse_le hc0 hc1 k ) ( show 0 ≤ M * a ^ k by positivity ) using 1;
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ show a ^ k = a ^ i * a ^ ( k - i ) by rw [ ← pow_add, Nat.add_sub_of_le ( Finset.mem_range_le hi ) ] ] ; ring;

/-- **Given**: recursion-tree upper estimate for Case 2. Needed by
`masterSeq_case2`. -/
theorem masterSeq_case2_sum_upper {a c₂ : ℝ} (ha : 1 ≤ a) {F : ℕ → ℝ}
    (hub : ∀ k, 1 ≤ k → F k ≤ c₂ * a ^ k) (k : ℕ) :
    ∑ i ∈ Finset.range k, a ^ i * F (k - i) ≤ c₂ * (k : ℝ) * a ^ k := by
  refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( hub _ <| Nat.sub_pos_of_lt <| Finset.mem_range.mp hi ) <| by positivity ) _;
  rw [ Finset.sum_congr rfl fun i hi => by rw [ mul_left_comm, ← pow_add, add_tsub_cancel_of_le ( Finset.mem_range_le hi ) ] ] ; norm_num ; ring_nf ; norm_num

/-- **Given**: recursion-tree lower estimate for Case 2. Needed by
`masterSeq_case2`. -/
theorem masterSeq_case2_sum_lower {a c₁ : ℝ} (ha : 1 ≤ a) {F : ℕ → ℝ}
    (hlb : ∀ k, 1 ≤ k → c₁ * a ^ k ≤ F k) (k : ℕ) :
    c₁ * (k : ℝ) * a ^ k ≤ ∑ i ∈ Finset.range k, a ^ i * F (k - i) := by
  have h_sum_bound : ∑ i ∈ Finset.range k, a ^ i * F (k - i) ≥ ∑ i ∈ Finset.range k, a ^ i * c₁ * a ^ (k - i) := by
    exact Finset.sum_le_sum fun i hi => by rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( hlb _ <| Nat.sub_pos_of_lt <| Finset.mem_range.mp hi ) <| by positivity;
  convert h_sum_bound.le using 1 ; ring_nf;
  rw [ Finset.sum_congr rfl fun i hi => by rw [ mul_assoc, ← pow_add, add_tsub_cancel_of_le ( Finset.mem_range_le hi ) ] ] ; norm_num ; ring

/-- **Given**: nonnegativity of the recurrence under Case 2's lower bound.
Needed by `masterSeq_case2`. -/
theorem masterSeq_nonneg_of_case2_lower {a d c₁ : ℝ} (ha : 1 ≤ a) (hd : 0 < d)
    (hc₁ : 0 < c₁) {F : ℕ → ℝ} (hlb : ∀ k, 1 ≤ k → c₁ * a ^ k ≤ F k) (k : ℕ) :
    0 ≤ masterSeq a d F k := by
  induction' k with k ih <;> simp_all +decide [ masterSeq ];
  · positivity;
  · exact add_nonneg ( mul_nonneg ( by positivity ) ih ) ( le_trans ( by positivity ) ( hlb _ ( Nat.succ_pos _ ) ) )

/-- The (real-valued) cost function extracted from a timed routine. -/
def timeCost {α : Type*} (run : ℕ → TimeM ℝ α) : ℕ → ℝ := fun n => (run n).time

/-- **Given**: extracting the time is definitionally the `.time` field.
Needed by `isBigO_of_timeCost_le`. -/
theorem timeCost_apply {α : Type*} (run : ℕ → TimeM ℝ α) (n : ℕ) :
    timeCost run n = (run n).time := rfl

/-- The cost function of a `ℕ`-cost routine, cast into `ℝ` so the Landau
relations apply. -/
def natTimeCost {α : Type*} (run : ℕ → TimeM ℕ α) : ℕ → ℝ := fun n => ((run n).time : ℝ)

/-! ## Lab 12 — complexity of sorting algorithms in the `TimeM` monad -/

open List (Perm)

scoped infixl:50 " ~ " => List.Perm

/-- The `n`-th triangular number `0 + 1 + … + (n-1) = n(n-1)/2`, as a
`Finset` sum so its recurrence `tri (n+1) = tri n + n` is definitional. -/
def tri (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, i

/-- **Given**: `tri` telescopes: `tri (n+1) = tri n + n`. Played
(re-derived) in the "Triangular Number Cost" level; supplied here so
`selectionSortT_time` can cite it. -/
theorem tri_succ (n : ℕ) : tri (n + 1) = tri n + n := by
  simp only [tri, Finset.sum_range_succ]

/-- Insert `x` into a list, charging one comparison per element inspected. -/
def insertT (x : ℕ) : List ℕ → TimeM ℕ (List ℕ)
  | [] => pure [x]
  | y :: ys => do
    TimeM.tick 1
    if x ≤ y then pure (x :: y :: ys)
    else do let r ← insertT x ys; pure (y :: r)

/-- Insertion sort: sort the tail, then insert the head. -/
def insertionSortT : List ℕ → TimeM ℕ (List ℕ)
  | [] => pure []
  | x :: xs => do
    let s ← insertionSortT xs
    insertT x s

/-- **Given**: `insertT` only rearranges elements. Played (re-derived) in
the "Insertion Correctness" level; supplied here so `insertionSortT_perm`
can cite it. -/
theorem insertT_perm (x : ℕ) (s : List ℕ) : (insertT x s).ret ~ x :: s := by
  induction' s with y ys ih;
  · rfl;
  · by_cases h : x ≤ y;
    · rw [ show insertT x ( y :: ys ) = do
        TimeM.tick 1
        if x ≤ y then pure ( x :: y :: ys ) else do let r ← insertT x ys; pure ( y :: r ) from rfl ] ; simp +decide only [h, ↓reduceIte, bind_pure_comp, TimeM.ret_map, Perm.refl];
    · rw [ show insertT x ( y :: ys ) = do { TimeM.tick 1; if x ≤ y then pure ( x :: y :: ys ) else do { let r ← insertT x ys; pure ( y :: r ) } } from rfl ] ; simp +decide only [h, ↓reduceIte, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map];
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

/-- **Given**: `insertT` preserves sortedness. Played (re-derived) in the
"Insertion Correctness" level; supplied here so `insertionSortT_sorted`
can cite it. -/
theorem insertT_sorted {x : ℕ} {s : List ℕ} (hs : s.Pairwise (· ≤ ·)) :
    (insertT x s).ret.Pairwise (· ≤ ·) := by
  induction' s with y ys ih;
  · exact List.pairwise_singleton _ _;
  · by_cases hxy : x ≤ y;
    · rw [ show insertT x ( y :: ys ) = do { TimeM.tick 1; if x ≤ y then pure ( x :: y :: ys ) else do { let r ← insertT x ys; pure ( y :: r ) } } from rfl ] ; simp +decide only [hxy, ↓reduceIte, bind_pure_comp, TimeM.ret_map, List.pairwise_cons, List.mem_cons, forall_eq_or_imp, true_and];
      obtain ⟨hy, htail⟩ := List.pairwise_cons.mp hs
      exact ⟨fun a ha => le_trans hxy (hy a ha), hy, htail⟩;
    · rw [ show insertT x ( y :: ys ) = do { TimeM.tick 1; if x ≤ y then pure ( x :: y :: ys ) else do { let r ← insertT x ys; pure ( y :: r ) } } from rfl ] ; simp +decide only [hxy, ↓reduceIte, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map, List.pairwise_cons];
      refine' ⟨ _, ih _ ⟩;
      · intro a' ha'
        have h_mem : a' ∈ x :: ys := by
          exact List.Perm.subset ( insertT_perm x ys ) ha';
        rcases List.mem_cons.mp h_mem with rfl | hys
        · exact le_of_lt (not_le.mp hxy)
        · exact (List.pairwise_cons.mp hs).1 a' hys
      · exact List.pairwise_cons.mp hs |>.2

/-- **Given**: insertion sort only rearranges elements. Needed by
`sortsAgree`. -/
theorem insertionSortT_perm (l : List ℕ) : (insertionSortT l).ret ~ l := by
  induction' l with x xs ih;
  · exact List.Perm.refl _;
  · convert List.Perm.trans ( insertT_perm x _ ) ( List.Perm.cons x ih ) using 1

/-- **Given**: insertion sort returns a sorted list. Needed by
`sortsAgree`. -/
theorem insertionSortT_sorted (l : List ℕ) : (insertionSortT l).ret.Pairwise (· ≤ ·) := by
  induction' l with x xs ih;
  · exact List.Pairwise.nil;
  · convert insertT_sorted ih using 1

/-- **Given**: length preserved by insertion sort. Needed by
`insertionSortT_time_le`. -/
theorem insertionSortT_length (l : List ℕ) : (insertionSortT l).ret.length = l.length := by
  exact List.Perm.length_eq ( insertionSortT_perm l )

/-- **Given**: `insertT` never costs more than the list length. Needed by
`insertionSortT_time_le`. -/
theorem insertT_time_le (x : ℕ) (s : List ℕ) : (insertT x s).time ≤ s.length := by
  induction' s with y ys ih generalizing x <;> simp +decide only [List.length_nil, nonpos_iff_eq_zero, List.length_cons];
  · rfl;
  · unfold insertT; split_ifs <;> simp +arith +decide only [bind_pure_comp, TimeM.time_map, TimeM.time_tick, le_add_iff_nonneg_left, zero_le, TimeM.time_bind, ih] ;

/-- `extractMin x l` returns the minimum of `x :: l` together with the
remaining elements. -/
def extractMin : ℕ → List ℕ → ℕ × List ℕ
  | x, [] => (x, [])
  | x, y :: ys =>
      let (m, rest) := extractMin y ys
      if x ≤ m then (x, y :: ys) else (m, x :: rest)

/-- **Given**: `extractMin` returns a rest of the same length as its list
argument. Needed by `selectionSortT`'s own termination proof and by
`selectionSortT_time`. -/
theorem extractMin_length (x : ℕ) (l : List ℕ) : (extractMin x l).2.length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih => simp only [extractMin]; split <;> simp [ih]

/-- Selection sort: extract the minimum (costing `length - 1` comparisons),
then recurse. -/
def selectionSortT : List ℕ → TimeM ℕ (List ℕ)
  | [] => pure []
  | x :: xs =>
    let p := extractMin x xs
    do
      TimeM.tick xs.length
      let s ← selectionSortT p.2
      pure (p.1 :: s)
  termination_by l => l.length
  decreasing_by
    have h := extractMin_length x xs
    exact Nat.lt_succ_of_le (le_of_eq h)

/-- **Given**: `extractMin`'s minimum and rest form a permutation of the
original input. Needed by `selectionSortT_perm`. -/
theorem extractMin_perm (x : ℕ) (l : List ℕ) : (extractMin x l).1 :: (extractMin x l).2 ~ x :: l := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih =>
    have hih := ih y
    rw [extractMin]
    rcases h : extractMin y ys with ⟨m, rest⟩
    rw [h] at hih
    dsimp only
    split_ifs with hle
    · exact List.Perm.refl _
    · exact (List.Perm.swap x m rest).trans (List.Perm.cons x hih)

/-- **Given**: the extracted minimum is `≤` the seed and `≤` every element
of the list. Needed by `extractMin_le`. -/
theorem extractMin_fst_le (x : ℕ) (l : List ℕ) :
    (extractMin x l).1 ≤ x ∧ ∀ z ∈ l, (extractMin x l).1 ≤ z := by
  induction l generalizing x with
  | nil => exact ⟨le_refl x, fun z hz => by cases hz⟩
  | cons y ys ih =>
    have hih := ih y
    rw [extractMin]; rcases h : extractMin y ys with ⟨m, rest⟩; rw [h] at hih; dsimp only
    split_ifs with hle
    · refine ⟨le_refl x, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hzys
      · exact le_trans hle hih.1
      · exact le_trans hle (hih.2 z hzys)
    · refine ⟨le_of_lt (not_le.mp hle), fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hzys
      · exact hih.1
      · exact hih.2 z hzys

/-- **Given**: every remaining element after extraction is `≥` the
extracted minimum. Needed by `selectionSortT_sorted`. -/
theorem extractMin_le (x : ℕ) (l : List ℕ) :
    ∀ y ∈ (extractMin x l).2, (extractMin x l).1 ≤ y := by
  intro z hz
  have hzmem : z ∈ x :: l := (extractMin_perm x l).subset (List.mem_cons_of_mem _ hz)
  rcases List.mem_cons.mp hzmem with heq | hzl
  · rw [heq]; exact (extractMin_fst_le x l).1
  · exact (extractMin_fst_le x l).2 z hzl

/-- **Given**: selection sort only rearranges elements. Played (re-derived)
in the "Selection Correctness" level; supplied here so `sortsAgree` can
cite it. -/
theorem selectionSortT_perm (l : List ℕ) : (selectionSortT l).ret ~ l := by
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide only [List.length_nil, List.perm_nil, List.length_cons, zero_add, List.perm_singleton];
  · native_decide +revert;
  · unfold selectionSortT
    simp only [extractMin, List.length_nil, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map,
      selectionSortT, TimeM.ret_pure]
  · unfold selectionSortT;
    convert List.Perm.trans ( List.Perm.cons _ ( ih _ _ _ rfl ) ) ( extractMin_perm _ _ ) using 1;
    rw [ extractMin_length ] ; simp +arith +decide only [List.length_cons, n, le_refl]

/-- **Given**: selection sort returns a sorted list. Out of scope for
"Selection Correctness" (bonus there); given whole since `sortsAgree`
needs it. -/
theorem selectionSortT_sorted (l : List ℕ) : (selectionSortT l).ret.Pairwise (· ≤ ·) := by
  have h_ind : ∀ l, List.Pairwise (· ≤ ·) (selectionSortT l).ret := by
    intro l
    induction' n : l.length using Nat.strong_induction_on with n ih generalizing l
    rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide only [List.length_nil, List.length_cons, zero_add];
    · native_decide +revert;
    · unfold selectionSortT; simp +decide only [List.length_nil, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map, List.pairwise_cons] ;
      unfold selectionSortT; simp +decide only [extractMin, TimeM.ret_pure, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self] ;
    · unfold selectionSortT; simp +arith +decide only [List.length_cons, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map, List.pairwise_cons] ;
      refine' ⟨ _, ih _ _ _ rfl ⟩;
      · intro a' ha'
        have h_mem : a' ∈ (extractMin x (y :: l)).2 := by
          exact List.Perm.subset ( selectionSortT_perm _ ) ha'
        exact extractMin_le x (y :: l) a' h_mem;
      · rw [ extractMin_length ] ; simp +arith +decide only [List.length_cons, n, le_refl];
  exact h_ind l

/-- **Given**: exact cost of selection sort — always `tri l.length`
comparisons. Played (re-derived) in the "Exact and Worst Costs" level;
supplied here so cross-references stay consistent. -/
theorem selectionSortT_time (l : List ℕ) : (selectionSortT l).time = tri l.length := by
  have h_ind : ∀ (l : List ℕ), (selectionSortT l).time = tri l.length := by
    intro l;
    induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
    rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide only [List.length_nil, List.length_cons, zero_add];
    · rw [← n]; unfold selectionSortT; simp only [TimeM.time_pure]; rfl
    · rw [← n]; unfold selectionSortT
      simp only [extractMin, List.length_nil, bind_pure_comp, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_map, selectionSortT, TimeM.time_pure]; rfl
    · unfold selectionSortT; simp +arith +decide only [List.length_cons, bind_pure_comp, TimeM.time_bind, TimeM.time_tick, TimeM.time_map] ;
      rw [ih ((extractMin x (y :: l)).2).length
          (by rw [extractMin_length]; simp only [List.length_cons]; omega) _ rfl,
        extractMin_length, List.length_cons, ← n]
      simp only [tri_succ]; omega
  exact h_ind l

/-- Quick sort with the head as pivot; partitioning costs one comparison
per non-pivot element. -/
def quickSortT : List ℕ → TimeM ℕ (List ℕ)
  | [] => pure []
  | p :: xs => do
    TimeM.tick xs.length
    let slo ← quickSortT (xs.filter (fun a => a ≤ p))
    let shi ← quickSortT (xs.filter (fun a => ¬ a ≤ p))
    pure (slo ++ p :: shi)
  termination_by l => l.length
  decreasing_by
    all_goals
      apply Nat.lt_succ_of_le
      rw [List.length_unattach]
      exact le_trans (List.length_filter_le _ _) (le_of_eq (List.length_attach))

/-- **Given**: filtering `xs` by `≤ p` and by `> p` partitions it, so their
element counts add back to `xs`. Played (re-derived) in the "Quick
Partition" level; supplied here so `quickSortT_perm` can cite it. -/
theorem filter_count_partition (xs : List ℕ) (p a : ℕ) :
    List.count a (xs.filter (fun b => decide (b ≤ p)))
      + List.count a (xs.filter (fun b => decide (p < b))) = List.count a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ≤ p
    · rw [List.filter_cons_of_pos (by simp [hx]), List.filter_cons_of_neg (by simp; omega),
        List.count_cons, List.count_cons]
      omega
    · rw [List.filter_cons_of_neg (by simp [hx]), List.filter_cons_of_pos (by simp; omega),
        List.count_cons, List.count_cons]
      omega

/-- **Given**: quick sort only rearranges elements. Needed by
`sortsAgree`. -/
theorem quickSortT_perm (l : List ℕ) : (quickSortT l).ret ~ l := by
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  rcases l with ( _ | ⟨ p, xs ⟩ ) <;> simp_all +decide only [List.length_nil, List.perm_nil, List.length_cons];
  · native_decide +revert;
  · unfold quickSortT; simp +decide only [not_le, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map, List.perm_iff_count, List.count_append] ;
    intro a
    have hlo := ih (xs.filter (fun a => decide (a ≤ p))).length
      (by have := List.length_filter_le (fun a => decide (a ≤ p)) xs; omega) _ rfl
    have hhi := ih (xs.filter (fun a => decide (p < a))).length
      (by have := List.length_filter_le (fun a => decide (p < a)) xs; omega) _ rfl
    rw [List.count_cons, List.count_cons, hlo.count_eq, hhi.count_eq]
    have hpart := filter_count_partition xs p a
    omega

/-- **Given**: quick sort returns a sorted list. Needed by
`sortsAgree`. -/
theorem quickSortT_sorted (l : List ℕ) : (quickSortT l).ret.Pairwise (· ≤ ·) := by
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  unfold quickSortT;
  rcases l with ( _ | ⟨ p, xs ⟩ ) <;> simp_all +decide only [not_le, List.length_nil, List.length_cons, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map, List.pairwise_append, List.pairwise_cons, List.mem_cons, forall_eq_or_imp];
  refine' ⟨ ih _ _ _ rfl, ⟨ _, ih _ _ _ rfl ⟩, _ ⟩;
  · exact lt_of_le_of_lt ( List.length_filter_le _ _ ) ( by linarith );
  · intro a' ha'
    have h_mem : a' ∈ xs.filter (fun a => p < a) := by
      exact List.Perm.subset ( quickSortT_perm _ ) ha';
    exact le_of_lt (of_decide_eq_true (List.mem_filter.mp h_mem).2);
  · exact lt_of_le_of_lt ( List.length_filter_le _ _ ) ( by linarith );
  · intro a ha
    have h_a_le_p : a ≤ p := by
      have h_a_le_p : a ∈ List.filter (fun a => decide (a ≤ p)) xs := by
        exact List.Perm.subset ( quickSortT_perm _ ) ha;
      exact of_decide_eq_true (List.mem_filter.mp h_a_le_p).2
    have h_a_le_b : ∀ b ∈ (quickSortT (List.filter (fun a => decide (p < a)) xs)).ret, a ≤ b := by
      intro b hb
      have h_b_gt_p : p < b := by
        have h_b_gt_p : b ∈ List.filter (fun a => decide (p < a)) xs := by
          exact List.Perm.subset ( quickSortT_perm _ ) hb;
        exact of_decide_eq_true (List.mem_filter.mp h_b_gt_p).2
      exact le_trans h_a_le_p (le_of_lt h_b_gt_p)
    exact ⟨h_a_le_p, h_a_le_b⟩

/-- The merge-sort running time as a function of input length
(value-independent in our cost model). -/
def mstime : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => (n + 2) + mstime ((n + 2) / 2) + mstime ((n + 2) - (n + 2) / 2)
  termination_by n => n
  decreasing_by all_goals omega

/-- **Given**: the defining recurrence of `mstime`, valid for `n ≥ 2`.
Needed by `mstime_pow`, `mstime_le`, `mstime_ge`. -/
theorem mstime_rec {n : ℕ} (hn : 2 ≤ n) :
    mstime n = n + mstime (n / 2) + mstime (n - n / 2) := by
  rcases n with ( _ | _ | n ) <;> simp_all +arith +decide only [le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, Nat.add_div_right, Nat.reduceSubDiff];
  rw [ mstime ]
  have h1 : (n + 2) / 2 = n / 2 + 1 := by omega
  have h2 : n + 2 - (n / 2 + 1) = n + 1 - n / 2 := by omega
  rw [h1, h2]; omega

/-- Merge sort: split in half (charging one unit per element for the
merge), recurse, merge. -/
def mergeSortT : List ℕ → TimeM ℕ (List ℕ)
  | [] => pure []
  | [a] => pure [a]
  | a :: b :: rest =>
    let l := a :: b :: rest
    let n := l.length
    do
      TimeM.tick n
      let s₁ ← mergeSortT (l.take (n / 2))
      let s₂ ← mergeSortT (l.drop (n / 2))
      pure (List.merge s₁ s₂ (fun a b => a ≤ b))
  termination_by l => l.length
  decreasing_by
    · simp only [List.length_take, List.length_cons]; omega
    · simp only [List.length_drop, List.length_cons]; omega

/-- **Given**: merge sort only rearranges elements. Needed by
`sortsAgree`. -/
theorem mergeSortT_perm (l : List ℕ) : (mergeSortT l).ret ~ l := by
  have h_merge_perm_append : ∀ (xs ys : List ℕ), (List.merge xs ys (fun x y => x ≤ y)).Perm (xs ++ ys) := by
    exact fun xs ys => List.merge_perm_append _;
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  unfold mergeSortT;
  rcases l with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide only [List.length_nil, List.length_cons, zero_add, TimeM.ret_pure, Perm.refl, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map];
  convert List.Perm.trans ( h_merge_perm_append _ _ ) ( List.Perm.append ( ih _ _ _ rfl ) ( ih _ _ _ rfl ) ) using 1;
  · rw [ List.take_append_drop ];
  · rw [List.length_take, List.length_cons, List.length_cons]; omega
  · simp +arith +decide only [← n, Nat.ofNat_pos, Nat.add_div_right, List.drop_succ_cons, List.length_drop, List.length_cons, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]

/-- **Given**: merge sort returns a sorted list. Needed by
`sortsAgree`. -/
theorem mergeSortT_sorted (l : List ℕ) : (mergeSortT l).ret.Pairwise (· ≤ ·) := by
  induction' n : l.length using Nat.strong_induction_on with n ih generalizing l;
  rcases l with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide only [List.length_nil, List.length_cons, zero_add];
  · native_decide +revert;
  · unfold mergeSortT; simp +decide only [TimeM.ret_pure, List.pairwise_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_self] ;
  · unfold mergeSortT;
    convert List.Pairwise.merge _ _ using 1;
    · exact ⟨ fun x y => le_total x y ⟩;
    · infer_instance;
    · exact ih _ (by rw [List.length_take, List.length_cons, List.length_cons]; omega) _ rfl
    · exact ih _ (by rw [List.length_drop, List.length_cons, List.length_cons]; omega) _ rfl

/-- **Given**: every routine returns the canonical non-decreasing
permutation, hence the four agree. Played (re-assembled) in the "Sorting
Agreement" boss level; supplied here in case a later world needs it. -/
theorem sorted_perm_unique {l₁ l₂ : List ℕ}
    (h₁ : l₁.Pairwise (· ≤ ·)) (h₂ : l₂.Pairwise (· ≤ ·)) (hp : l₁ ~ l₂) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba) h₁ h₂ hp

/-- **Given**: `mstime` on exact powers of two has the clean closed form
`k · 2^k`. Played (re-derived) in the "Merge Asymptotics" level; supplied
here in case a later world needs it. -/
theorem mstime_pow (k : ℕ) : mstime (2 ^ k) = k * 2 ^ k := by
  induction' k with k ih;
  · native_decide +revert;
  · convert mstime_rec ( show 2 ≤ 2 ^ ( k + 1 ) from ?_ ) using 1;
    · have hp : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have e1 : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [hp]; omega
      have e2 : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by rw [hp]; omega
      rw [e1, e2, ih]; simp only [hp]; ring
    · exact le_self_pow ( by norm_num ) ( by norm_num )

/-- **Given**: upper bound `mstime n ≤ n · ⌈log₂ n⌉`. Needed by
`mstime_isBigTheta_nlogn`. -/
theorem mstime_le (n : ℕ) : mstime n ≤ n * Nat.clog 2 n := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn : n < 2;
  · interval_cases n <;> native_decide +revert;
  · have h_bound : mstime (n / 2) ≤ (n / 2) * Nat.clog 2 (n - n / 2) ∧ mstime (n - n / 2) ≤ (n - n / 2) * Nat.clog 2 (n - n / 2) := by
      apply And.intro;
      · refine' le_trans ( ih _ _ ) _;
        · omega;
        · gcongr;
          omega;
      · exact ih _ (by omega);
    have h_log : Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
      convert Nat.clog_of_two_le ( show 2 ≤ 2 by norm_num ) ( show 2 ≤ n by linarith ) using 1;
      rw [show n - n / 2 = (n + 2 - 1) / 2 from by omega];
    rw [ mstime_rec ( by linarith ) ];
    nlinarith [ Nat.div_mul_le_self n 2, Nat.sub_add_cancel ( show n / 2 ≤ n from Nat.div_le_self _ _ ) ]

/-- **Given**: lower bound `n · ⌊log₂ n⌋ ≤ mstime n`. Needed by
`mstime_isBigTheta_nlogn`. -/
theorem mstime_ge (n : ℕ) : n * Nat.log 2 n ≤ mstime n := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n ) <;> simp +arith +decide only;
  rw [ mstime_rec ];
  · have := ih ( ( n + 2 ) / 2 ) ( Nat.div_lt_self ( Nat.succ_pos _ ) ( by norm_num ) ) ; ( have := ih ( n + 2 - ( n + 2 ) / 2 ) ( Nat.sub_lt ( Nat.succ_pos _ ) ( Nat.div_pos ( by linarith ) ( by norm_num ) ) ) ; ( norm_num at * ; ) );
    rw [ show Nat.log 2 ( n + 2 ) = Nat.log 2 ( n / 2 + 1 ) + 1 from ?_ ];
    · nlinarith [ Nat.div_mul_le_self n 2, Nat.sub_add_cancel ( show n / 2 + 1 ≤ n + 2 from by linarith [ Nat.div_mul_le_self n 2 ] ), show Nat.log 2 ( n + 2 - ( n / 2 + 1 ) ) ≥ Nat.log 2 ( n / 2 + 1 ) from Nat.log_mono_right <| by omega ];
    · rw [ Nat.log_eq_iff ] <;> norm_num;
      exact ⟨ by rw [ pow_succ' ] ; linarith [ Nat.div_mul_le_self n 2, Nat.pow_log_le_self 2 ( show n / 2 + 1 ≠ 0 by norm_num ) ], by rw [ pow_succ' ] ; linarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos, Nat.lt_pow_of_log_lt ( by norm_num ) ( show Nat.log 2 ( n / 2 + 1 ) < Nat.log 2 ( n / 2 + 1 ) + 1 by norm_num ) ] ⟩;
  · lia

/-- **Given**: `Nat.clog` is at most `Nat.log` plus one (base 2). Needed by
`mstime_isBigTheta_nlogn`. -/
theorem clog_le_log_succ (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
  rw [ Nat.clog_le_iff_le_pow ] <;> norm_num;
  exact Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ )

/-- **Given**: for `n ≥ 2`, `log n < (⌊log₂ n⌋ + 1) · log 2`. Needed by
`mstime_isBigTheta_nlogn`. -/
theorem log_lt_natLog_succ {n : ℕ} (h : 2 ≤ n) :
    Real.log n < (Nat.log 2 n + 1) * Real.log 2 := by
  rw [ ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_cast <;> try positivity;
  exact Nat.lt_pow_succ_log_self ( by decide ) _

/-! ## Lab 13 — the comparison-sort lower bound (decision trees) -/

/-- A binary comparison decision tree for sorting inputs of length `n`.
`leaf p` outputs the permutation `p`; `node i j l r` compares the elements
at positions `i` and `j`, continuing into `l` if `values[i] ≤ values[j]`
and into `r` otherwise. -/
inductive DTree (n : ℕ) where
  /-- Outputs the permutation `p` (the algorithm's final answer). -/
  | leaf : Equiv.Perm (Fin n) → DTree n
  /-- Compares positions `i` and `j`, branching into the left or right
  subtree. -/
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

variable {n : ℕ}

/-- Running the tree on an input `σ` (where `σ k` is the rank of the
element at position `k`). -/
def run (σ : Equiv.Perm (Fin n)) : DTree n → Equiv.Perm (Fin n)
  | .leaf p => p
  | .node i j l r => if σ i ≤ σ j then run σ l else run σ r

/-- The finite set of permutations that appear as outputs at the leaves of
the tree. -/
def outputs : DTree n → Finset (Equiv.Perm (Fin n))
  | .leaf p => {p}
  | .node _ _ l r => outputs l ∪ outputs r

/-- The number of leaves of the tree (the number of possible outputs). -/
def numLeaves : DTree n → ℕ
  | .leaf _ => 1
  | .node _ _ l r => numLeaves l + numLeaves r

/-- The height of the tree: the worst-case number of comparisons made on
any input. -/
def height : DTree n → ℕ
  | .leaf _ => 0
  | .node _ _ l r => 1 + max (height l) (height r)

/-- A tree sorts length-`n` inputs when, on every input `σ`, it outputs the
sorting permutation `σ⁻¹`. -/
def Sorts (t : DTree n) : Prop := ∀ σ : Equiv.Perm (Fin n), run σ t = σ⁻¹

/-- **Given**: every run ends at one of the tree's leaves, so its output is
one of the recorded outputs. Needed by `factorial_le_numLeaves`. -/
theorem run_mem_outputs (σ : Equiv.Perm (Fin n)) (t : DTree n) :
    run σ t ∈ outputs t := by
  induction' t with i j l r ihl ihr;
  · exact Finset.mem_singleton_self _;
  · unfold run outputs; split_ifs <;> simp_all +decide [ Finset.mem_union ] ;

/-- **Given**: the number of distinct outputs is at most the number of
leaves. Needed by `factorial_le_numLeaves`. -/
theorem outputs_card_le_numLeaves (t : DTree n) :
    (outputs t).card ≤ numLeaves t := by
  induction' t with i j l r ihl ihr;
  · simp only [outputs, numLeaves, Finset.card_singleton, le_refl]
  · exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add ihr ‹_› )

/-- **Given**: shape bound — a binary tree of height `h` has at most `2^h`
leaves. Played (re-derived) in the "Decision Leaves" level; supplied here
so `factorial_le_two_pow_height` can cite it. -/
theorem numLeaves_le_two_pow_height (t : DTree n) :
    numLeaves t ≤ 2 ^ height t := by
  induction' t with i j l r ihl ihr;
  · simp only [numLeaves, height, pow_zero, le_refl];
  · simp +arith +decide [ *, height ];
    exact le_trans ( add_le_add ihr ‹_› ) ( by rw [ pow_succ' ] ; exact by cases max_cases ( height r ) ( height ihl ) <;> linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℕ ) ≤ 2 ) ( by linarith : height r ≤ max ( height r ) ( height ihl ) ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℕ ) ≤ 2 ) ( by linarith : height ihl ≤ max ( height r ) ( height ihl ) ) ] )

/-- **Given**: information bound — a tree that sorts must have at least
`n!` leaves. Played (re-derived) in the "Decision Leaves" level; supplied
here so `factorial_le_two_pow_height` can cite it. -/
theorem factorial_le_numLeaves (t : DTree n) (h : Sorts t) :
    n.factorial ≤ numLeaves t := by
  refine' le_trans _ ( outputs_card_le_numLeaves t );
  have h_image : Finset.image (fun σ : Equiv.Perm (Fin n) => σ⁻¹) Finset.univ ⊆ outputs t := by
    exact Finset.image_subset_iff.mpr fun σ _ => h σ ▸ run_mem_outputs σ t;
  exact le_trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ; simp +decide [ Fintype.card_perm ] ) ( Finset.card_mono h_image )

/-- **Given**: combining the two bounds — a sorting tree has height at
least `log₂(n!)`, phrased as `n! ≤ 2 ^ height`. Needed by
`log_factorial_le_height_mul_log_two`. -/
theorem factorial_le_two_pow_height (t : DTree n) (h : Sorts t) :
    n.factorial ≤ 2 ^ height t :=
  le_trans (factorial_le_numLeaves t h) (numLeaves_le_two_pow_height t)

/-- **Given**: the pairing bound `nⁿ ≤ (n!)²`. Needed by
`mul_log_le_two_mul_log_factorial`. -/
theorem pow_self_le_factorial_sq (n : ℕ) : n ^ n ≤ (n.factorial) ^ 2 := by
  revert n;
  intro n
  have h_prod : (n.factorial)^2 = ∏ i ∈ Finset.range n, (i + 1) * (n - i) := by
    simp +decide [ sq, Finset.prod_mul_distrib ];
    exact Or.inl <| Nat.recOn n ( by norm_num ) fun n ih => by cases n <;> simp_all +decide [ Nat.factorial_succ, mul_comm, Finset.prod_range_succ' ] ;
  rw [ h_prod ];
  exact le_trans ( by norm_num ) ( Finset.prod_le_prod' fun i hi => show ( i + 1 ) * ( n - i ) ≥ n by nlinarith only [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show i ≤ n from Finset.mem_range_le hi ) ] )

/-- **Given**: taking logarithms, `n · log n ≤ 2 · log (n!)`. Needed by
`comparison_sort_lower_bound`. -/
theorem mul_log_le_two_mul_log_factorial (n : ℕ) :
    (n : ℝ) * Real.log n ≤ 2 * Real.log (n.factorial) := by
  rcases n with ( _ | n ) <;> norm_num;
  have h_log : Real.log ((n + 1) ^ (n + 1)) ≤ Real.log ((n + 1).factorial ^ 2) := by
    exact Real.log_le_log ( by positivity ) ( mod_cast pow_self_le_factorial_sq _ );
  rw [Real.log_pow, Real.log_pow] at h_log
  push_cast at h_log ⊢
  linarith [h_log]

/-- **Given**: from `n! ≤ 2 ^ height`, `log (n!) ≤ height · log 2`. Needed
by `comparison_sort_lower_bound`. -/
theorem log_factorial_le_height_mul_log_two (t : DTree n) (h : Sorts t) :
    Real.log (n.factorial) ≤ (height t : ℝ) * Real.log 2 := by
  convert Real.log_le_log ?_ ( show ( n.factorial : ℝ ) ≤ 2 ^ ( height t ) from ?_ ) using 1;
  · norm_num [ Real.log_pow ];
  · positivity;
  · exact_mod_cast factorial_le_two_pow_height t h

/-! ## Lab 14 — radix sort, a non-comparison sort -/

/-- The `k`-th base-`b` digit of `x`: `(x / bᵏ) mod b`. -/
def digit (b k x : ℕ) : ℕ := (x / b ^ k) % b

/-- The number formed by the low `k` digits of `x` in base `b`, i.e. `x mod bᵏ`. -/
def key (b k x : ℕ) : ℕ := x % b ^ k

/-- **Given**: every digit is `< b` (needs `b > 0`). Needed by
`bucketPass_sorted`. -/
theorem digit_lt {b : ℕ} (hb : 0 < b) (k x : ℕ) : digit b k x < b :=
  Nat.mod_lt _ hb

/-- **Given**: the low-`k`-digit key is `< bᵏ` (needs `b > 0`). Needed by
`bucketPass_sorted`. -/
theorem key_lt {b : ℕ} (hb : 0 < b) (k x : ℕ) : key b k x < b ^ k :=
  Nat.mod_lt _ (pow_pos hb k)

/-- **Given**: `key b 0 x = 0`. Needed by `radixSort_sorted_key`. -/
theorem key_zero (b x : ℕ) : key b 0 x = 0 := by
  simp [key, Nat.mod_one]

/-- **Given**: the mixed-radix recurrence `key b (k+1) x = digit b k x * bᵏ +
key b k x`. Needed by `bucketPass_sorted`. -/
theorem key_succ (b k x : ℕ) : key b (k + 1) x = digit b k x * b ^ k + key b k x := by
  unfold key digit
  conv_lhs => rw [pow_succ]
  rw [Nat.mod_mul]
  ring

/-- One stable distribution pass over digit `k`: send each element into the
bucket named by its `k`-th digit, buckets taken in increasing order
`0, 1, …, b-1`. -/
def bucketPass (b k : ℕ) (l : List ℕ) : List ℕ :=
  (List.range b).flatMap (fun j => l.filter (fun x => decide (digit b k x = j)))

/-- **Given**: a bucket pass is a permutation of its input. Played
(re-derived) in the "Stable Bucket" level; supplied here so
`bucketPass_length`/`radixPass_perm` can cite it. -/
theorem bucketPass_perm {b : ℕ} (hb : 0 < b) (k : ℕ) (l : List ℕ) :
    (bucketPass b k l) ~ l := by
  apply List.Perm.symm;
  by_contra h_contra;
  convert h_contra <| List.perm_iff_count.mpr ?_;
  intro a
  simp [bucketPass];
  rw [ List.count_flatMap ];
  rw [ List.sum_map_eq_nsmul_single ( digit b k a ) ] <;> simp +contextual [ Function.comp ];
  · exact fun h => absurd h ( not_le_of_gt ( digit_lt hb k a ) );
  · intro a' ha' ha''
    rw [List.count_eq_zero]
    intro hmem
    rw [List.mem_filter] at hmem
    exact ha' (of_decide_eq_true hmem.2).symm

/-- **Given**: a bucket pass preserves length. Needed by
`radixSortT_time`. -/
theorem bucketPass_length {b : ℕ} (hb : 0 < b) (k : ℕ) (l : List ℕ) :
    (bucketPass b k l).length = l.length :=
  (bucketPass_perm hb k l).length_eq

/-- **Given**: stability step — if `l` is already sorted by its low `k`
digits, one bucket pass over digit `k` leaves it sorted by its low `k+1`
digits. Needed by `radixPass_sorted`. -/
theorem bucketPass_sorted {b : ℕ} (hb : 0 < b) (k : ℕ) {l : List ℕ}
    (h : l.Pairwise (fun x y => key b k x ≤ key b k y)) :
    (bucketPass b k l).Pairwise (fun x y => key b (k + 1) x ≤ key b (k + 1) y) := by
  rw [ bucketPass ];
  rw [ List.pairwise_flatMap ];
  constructor;
  · intro a ha; rw [ List.pairwise_filter ] ; simp_all +decide [ key_succ ] ;
    exact h.imp fun x _ _ => x
  · rw [ List.pairwise_iff_get ];
    intro i j hij x hx y hy; rw [ key_succ, key_succ ] ; simp_all +decide [ List.mem_filter ] ;
    nlinarith [ show ( i : ℕ ) < j from hij, show key b k x < b ^ k from key_lt hb k x, show key b k y < b ^ k from key_lt hb k y, pow_pos hb k ]

/-- `radixPass b k n l` applies `n` consecutive bucket passes over digits
`k, k+1, …, k+n-1`. -/
def radixPass (b k : ℕ) : ℕ → List ℕ → List ℕ
  | 0,     l => l
  | n + 1, l => radixPass b (k + 1) n (bucketPass b k l)

/-- **LSD radix sort** with base `b` and `d` digit passes (digits `0 … d-1`,
least significant first). -/
def radixSort (b d : ℕ) (l : List ℕ) : List ℕ := radixPass b 0 d l

/-- **Given**: a run of `n` passes is a permutation of its input. Needed by
`radixSort_perm`. -/
theorem radixPass_perm {b : ℕ} (hb : 0 < b) (n : ℕ) :
    ∀ (k : ℕ) (l : List ℕ), radixPass b k n l ~ l := by
  induction' n with n ih generalizing b
  · intro k l; simp [radixPass]
  · exact fun k l => List.Perm.trans (ih hb _ _) (bucketPass_perm hb _ _)

/-- **Given**: invariant maintenance across all passes — if `l` is sorted
by its low `k` digits, then after `n` more passes it is sorted by its low
`k+n` digits. Needed by `radixSort_sorted_key`. -/
theorem radixPass_sorted {b : ℕ} (hb : 0 < b) (n : ℕ) :
    ∀ (k : ℕ) {l : List ℕ}, l.Pairwise (fun x y => key b k x ≤ key b k y) →
      (radixPass b k n l).Pairwise (fun x y => key b (k + n) x ≤ key b (k + n) y) := by
  induction' n with n ih generalizing b;
  · intro k l hl; rw [Nat.add_zero, radixPass]; exact hl
  · intro k l hl; rw [ show k + ( n + 1 ) = k + 1 + n by ring ] ; exact ih hb ( k + 1 ) ( bucketPass_sorted hb k hl ) ;

/-- **Given**: radix sort returns a permutation of its input. Needed by
`radix_agrees_with_mergeSort`. -/
theorem radixSort_perm {b : ℕ} (hb : 0 < b) (d : ℕ) (l : List ℕ) :
    radixSort b d l ~ l :=
  radixPass_perm hb d 0 l

/-- **Given**: radix sort leaves the list sorted by its low `d` digits.
Needed by `radixSort_sorted`. -/
theorem radixSort_sorted_key {b : ℕ} (hb : 0 < b) (d : ℕ) (l : List ℕ) :
    (radixSort b d l).Pairwise (fun x y => key b d x ≤ key b d y) := by
  have h0 : l.Pairwise (fun x y => key b 0 x ≤ key b 0 y) := by
    have heq : (fun x y : ℕ => key b 0 x ≤ key b 0 y) = (fun _ _ => True) := by
      funext x y; simp [key_zero]
    rw [heq]; exact List.pairwise_of_forall_sublist fun _ => trivial
  simpa using radixPass_sorted hb d 0 h0

/-- **Given**: correctness — when every key is `< bᵈ`, radix sort returns a
genuinely non-decreasing list. Played (re-derived) in the "Radix
Correctness" level; supplied here so `radix_agrees_with_mergeSort` can
cite it. -/
theorem radixSort_sorted {b : ℕ} (hb : 0 < b) (d : ℕ) {l : List ℕ}
    (hbound : ∀ x ∈ l, x < b ^ d) :
    (radixSort b d l).Pairwise (· ≤ ·) := by
  refine' List.Pairwise.imp_of_mem _ ( radixSort_sorted_key hb d l );
  intro x y hx hy hxy; rw [ show key b d x = x from Nat.mod_eq_of_lt <| hbound x <| by simpa using ( radixSort_perm hb d l ).subset hx ] at hxy; rw [ show key b d y = y from Nat.mod_eq_of_lt <| hbound y <| by simpa using ( radixSort_perm hb d l ).subset hy ] at hxy; linarith;

/-- **Given**: equivalence in results — on inputs whose keys fit in `d`
base-`b` digits, radix sort returns exactly the same list as merge sort.
Played (re-derived) in the "Radix Correctness" level; supplied here in
case a later world needs it. -/
theorem radix_agrees_with_mergeSort {b : ℕ} (hb : 0 < b) (d : ℕ) {l : List ℕ}
    (hbound : ∀ x ∈ l, x < b ^ d) :
    radixSort b d l = (mergeSortT l).ret := by
  refine sorted_perm_unique (radixSort_sorted hb d hbound) (mergeSortT_sorted l) ?_
  exact (radixSort_perm hb d l).trans (mergeSortT_perm l).symm

/-- Timed radix sort: one `tick` of `length`-many units per digit pass. -/
def radixSortT (b k : ℕ) : ℕ → List ℕ → TimeM ℕ (List ℕ)
  | 0,     l => pure l
  | n + 1, l => do
      TimeM.tick l.length
      radixSortT b (k + 1) n (bucketPass b k l)

/-- **Given**: the timed routine returns the same list as the pure
`radixPass`. Not needed elsewhere, but recorded for completeness. -/
theorem radixSortT_ret {b : ℕ} (n : ℕ) :
    ∀ (k : ℕ) (l : List ℕ), (radixSortT b k n l).ret = radixPass b k n l := by
  induction' n with n ih
  · intro k l; rfl
  · intro k l
    simp only [radixSortT, radixPass, TimeM.ret_bind, ih]

/-- **Given**: running time — `d` passes over a length-`n` list cost
exactly `d * n`. Played (re-derived) in the "Radix Sort Correctness" level; supplied
here so `radixSort_time` can cite it. -/
theorem radixSortT_time {b : ℕ} (hb : 0 < b) (n : ℕ) :
    ∀ (k : ℕ) (l : List ℕ), (radixSortT b k n l).time = n * l.length := by
  induction' n with n ih;
  · intro k l; rw [radixSortT, TimeM.time_pure, Nat.zero_mul]
  · intro k l; rw [ radixSortT ] ; simp +decide [ ih, bucketPass_length hb ] ; ring;

/-- **Given**: specialised to `radixSort` — the whole sort costs `d * n`.
Played (re-derived) in the "Radix Sort Correctness" level; supplied here in case a
later world needs it. -/
theorem radixSort_time {b : ℕ} (hb : 0 < b) (d : ℕ) (l : List ℕ) :
    (radixSortT b 0 d l).time = d * l.length :=
  radixSortT_time hb d 0 l

/-! ## Lab 15 — heapsort and the heap invariant -/

/-- A binary tree of natural numbers used as a (max-)heap. -/
inductive Heap where
  /-- The empty heap. -/
  | nil : Heap
  /-- A root key with a left and right subtree. -/
  | node : Heap → ℕ → Heap → Heap
  deriving Repr

/-- The multiset of elements of a heap, as a list (root first, then the
two subtrees). -/
def elems : Heap → List ℕ
  | .nil => []
  | .node l x r => x :: (elems l ++ elems r)

/-- The number of elements of a heap. -/
def size : Heap → ℕ
  | .nil => 0
  | .node l _x r => size l + size r + 1

@[simp] theorem elems_nil : elems .nil = [] := rfl
@[simp] theorem elems_node (l : Heap) (x : ℕ) (r : Heap) :
    elems (.node l x r) = x :: (elems l ++ elems r) := rfl
@[simp] theorem size_nil : size .nil = 0 := rfl
@[simp] theorem size_node (l : Heap) (x : ℕ) (r : Heap) :
    size (.node l x r) = size l + size r + 1 := rfl

/-- **The max-heap invariant.** At every node, the stored key dominates
all keys in both subtrees, and both subtrees are themselves heaps. -/
def IsHeap : Heap → Prop
  | .nil => True
  | .node l x r => (∀ y ∈ elems l, y ≤ x) ∧ (∀ y ∈ elems r, y ≤ x) ∧ IsHeap l ∧ IsHeap r

@[simp] theorem isHeap_nil : IsHeap .nil := trivial

/-- Unfolds `IsHeap` at a `node`: the root dominates both subtrees, and
both subtrees are themselves heaps. -/
theorem isHeap_node_iff (l : Heap) (x : ℕ) (r : Heap) :
    IsHeap (.node l x r) ↔
      (∀ y ∈ elems l, y ≤ x) ∧ (∀ y ∈ elems r, y ≤ x) ∧ IsHeap l ∧ IsHeap r := Iff.rfl

/-- **Given**: in a heap, the root key dominates every element. Not needed
elsewhere, but recorded for completeness. -/
theorem IsHeap.le_root {l : Heap} {x : ℕ} {r : Heap} (h : IsHeap (.node l x r)) :
    ∀ y ∈ elems (.node l x r), y ≤ x := by
  simp_all +decide [ isHeap_node_iff ];
  rintro a ( ha | ha ) <;> [ exact h.1 a ha; exact h.2.1 a ha ]

/-- Fuse two heaps. Compare the two roots, keep the larger as the new
root, and recursively merge into it — swapping the children as we descend
(the "skew heap" trick that keeps things shallow). -/
def merge : Heap → Heap → Heap
  | .nil, h => h
  | h, .nil => h
  | .node l₁ x₁ r₁, .node l₂ x₂ r₂ =>
      if x₂ ≤ x₁ then .node (merge r₁ (.node l₂ x₂ r₂)) x₁ l₁
      else .node (merge r₂ (.node l₁ x₁ r₁)) x₂ l₂
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by all_goals (simp_wf <;> omega)

@[simp] theorem merge_nil_left (h : Heap) : merge .nil h = h := by simp [merge]
@[simp] theorem merge_nil_right (h : Heap) : merge h .nil = h := by cases h <;> simp [merge]

/-- **Given**: `merge` keeps every element — its output is a permutation
of the two inputs concatenated. Not played as a separate level (its
`Sorry`-free proof needs strong induction on the combined size), but
supplied since `merge_isHeap`, `buildHeap`'s and `popAll`'s facts all rely
on it. -/
theorem elems_merge (a b : Heap) : elems (merge a b) ~ elems a ++ elems b := by
  induction' n : size a + size b using Nat.strong_induction_on with n ih generalizing a b;
  rcases a with ( _ | ⟨ l₁, x₁, r₁ ⟩ ) <;> rcases b with ( _ | ⟨ l₂, x₂, r₂ ⟩ ) <;> simp_all +decide [ merge ];
  split_ifs <;> simp_all +decide [ List.perm_iff_count ];
  · intro a; specialize ih ( size r₁ + ( size l₂ + size r₂ + 1 ) ) ( by linarith ) r₁ ( l₂.node x₂ r₂ ) rfl a; simp_all +decide [ List.count_cons ] ;
    ring
  · intro a; specialize ih ( size r₂ + size ( l₁.node x₁ r₁ ) ) ( by simp +arith +decide [ size ] ; linarith ) r₂ ( l₁.node x₁ r₁ ) rfl a; simp_all +decide [ List.count_cons ] ;
    ring

/-- **Given**: `merge` preserves size (it drops nothing). Needed by
`merge_isHeap`. -/
theorem size_merge (a b : Heap) : size (merge a b) = size a + size b := by
  induction' n : size a + size b using Nat.strong_induction_on with n ih generalizing a b; rcases a with ( _ | ⟨ l₁, x₁, r₁ ⟩ ) <;> rcases b with ( _ | ⟨ l₂, x₂, r₂ ⟩ ) ; simp_all +decide ;
  · rw [merge_nil_left]; have : size Heap.nil = 0 := rfl; omega
  · rw [merge_nil_right]; have : size Heap.nil = 0 := rfl; omega
  · unfold merge
    split_ifs with h <;>
      simp only [size] <;>
      [rw [ih (size r₁ + size (l₂.node x₂ r₂)) (by simp only [size] at n ⊢; omega) r₁ _ rfl];
       rw [ih (size r₂ + size (l₁.node x₁ r₁)) (by simp only [size] at n ⊢; omega) r₂ _ rfl]] <;>
      simp only [size] at n ⊢ <;> omega

/-- **Given**: invariant maintenance (the centrepiece) — merging two heaps
yields a heap. Played (re-derived) in the "Heap Invariant" level; supplied
here so `insert_isHeap` can cite it. -/
theorem merge_isHeap {a b : Heap} (ha : IsHeap a) (hb : IsHeap b) : IsHeap (merge a b) := by
  have h_ind : ∀ (s : ℕ), (∀ (a b : Heap), size a + size b < s → IsHeap a → IsHeap b → IsHeap (merge a b)) → ∀ (a b : Heap), size a + size b = s → IsHeap a → IsHeap b → IsHeap (merge a b) := by
    rintro s ih a b rfl ha hb; rcases a with ( _ | ⟨ l₁, x₁, r₁ ⟩ ) <;> rcases b with ( _ | ⟨ l₂, x₂, r₂ ⟩ ) <;> simp_all +decide ;
    unfold merge; split_ifs <;> simp_all +decide [ isHeap_node_iff ];
    · intro y hy
      have hy2 := (elems_merge r₁ (l₂.node x₂ r₂)).mem_iff.mp hy
      rw [List.mem_append, elems, List.mem_cons, List.mem_append] at hy2
      rcases hy2 with h | h | h | h
      · exact ha.2.1 y h
      · exact le_of_eq_of_le h ‹x₂ ≤ x₁›
      · exact le_trans (hb.1 y h) ‹x₂ ≤ x₁›
      · exact le_trans (hb.2.1 y h) ‹x₂ ≤ x₁›
    · refine' ⟨ _, ih _ _ _ _ _ ⟩;
      · intro y hy
        have hy2 := (elems_merge r₂ (l₁.node x₁ r₁)).mem_iff.mp hy
        rw [List.mem_append, elems, List.mem_cons, List.mem_append] at hy2
        have hx : x₁ ≤ x₂ := ‹x₁ < x₂›.le
        rcases hy2 with h | h | h | h
        · exact hb.2.1 y h
        · exact le_of_eq_of_le h hx
        · exact le_trans (ha.1 y h) hx
        · exact le_trans (ha.2.1 y h) hx
      · simp +arith +decide [ size ];
      · tauto;
      · exact ⟨ ha.1, ha.2.1, ha.2.2.1, ha.2.2.2 ⟩;
  have h_ind : ∀ (s : ℕ), ∀ (a b : Heap), size a + size b = s → IsHeap a → IsHeap b → IsHeap (merge a b) := by
    intro s; induction' s using Nat.strong_induction_on with s ih; exact h_ind s (fun a b hab ha hb => ih _ hab a b rfl ha hb);
  exact h_ind _ _ _ rfl ha hb

/-- The one-element heap. -/
def singleton (x : ℕ) : Heap := .node .nil x .nil

@[simp] theorem elems_singleton (x : ℕ) : elems (singleton x) = [x] := rfl
@[simp] theorem isHeap_singleton (x : ℕ) : IsHeap (singleton x) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [elems]

/-- Insert one key by merging in a singleton heap. -/
def heapInsert (x : ℕ) (h : Heap) : Heap := merge (singleton x) h

/-- **Given**: insertion maintains the heap invariant. Needed by
`buildHeap_isHeap`. -/
theorem insert_isHeap (x : ℕ) {h : Heap} (hh : IsHeap h) : IsHeap (heapInsert x h) :=
  merge_isHeap (isHeap_singleton x) hh

/-- **Given**: insertion adds exactly the new key. Needed by
`elems_buildHeap`. -/
theorem elems_insert (x : ℕ) (h : Heap) : elems (heapInsert x h) ~ x :: elems h := by
  convert elems_merge ( singleton x ) h using 1

/-- Build a heap from a list by repeated insertion. -/
def buildHeap (l : List ℕ) : Heap := l.foldr heapInsert .nil

/-- **Given**: building a heap maintains the invariant at every step.
Played (re-derived) in the "Heap Construction" level; supplied here so
`popAllFuel_sorted` can cite it. -/
theorem buildHeap_isHeap (l : List ℕ) : IsHeap (buildHeap l) := by
  induction' l with x l ih
  · trivial
  · convert insert_isHeap x ih using 1

/-- **Given**: building a heap loses no elements. Played (re-derived) in
the "Heap Construction" level; supplied here so `heapSort_perm` can cite
it. -/
theorem elems_buildHeap (l : List ℕ) : elems (buildHeap l) ~ l := by
  induction' l with x l ih;
  · rfl;
  · convert List.Perm.trans ( elems_insert x ( buildHeap l ) ) ( List.Perm.cons x ih ) using 1

/-- Remove the maximum (the root) and re-merge the two subtrees. Driven by
an explicit fuel counter so the recursion is manifestly terminating;
`size` fuel is always enough (see `popAll`). -/
def popAllFuel : ℕ → Heap → List ℕ
  | 0, _ => []
  | _ + 1, .nil => []
  | fuel + 1, .node l x r => x :: popAllFuel fuel (merge l r)

/-- Repeatedly pop the maximum until the heap is empty. -/
def popAll (h : Heap) : List ℕ := popAllFuel (size h) h

/-- **Given**: with enough fuel, popping is a permutation of the heap's
elements. Needed by `popAll_perm`. -/
theorem popAllFuel_perm (fuel : ℕ) (h : Heap) (hf : size h ≤ fuel) :
    popAllFuel fuel h ~ elems h := by
  induction' fuel with fuel ih generalizing h;
  · cases h <;> trivial;
  · rcases h with ( _ | ⟨ l, x, r ⟩ ) <;> simp_all +arith +decide [ size ];
    · rfl;
    · convert List.Perm.trans ( List.Perm.cons x ( ih ( merge l r ) _ ) ) ( List.Perm.cons x ( elems_merge l r ) ) using 1;
      rw [ size_merge ] ; linarith

/-- **Given**: popping loses no elements. Needed by `heapSort_perm`. -/
theorem popAll_perm (h : Heap) : popAll h ~ elems h :=
  popAllFuel_perm (size h) h le_rfl

/-- **Given**: with enough fuel, popping a heap yields a list sorted in
decreasing order. Needed by `popAll_sorted`. -/
theorem popAllFuel_sorted (fuel : ℕ) (h : Heap) (hf : size h ≤ fuel) (hh : IsHeap h) :
    (popAllFuel fuel h).Pairwise (· ≥ ·) := by
  induction' fuel with fuel ih generalizing h;
  · cases h <;> trivial;
  · rcases h with ( _ | ⟨ l, x, r ⟩ ) <;> simp_all +arith +decide [ size ];
    · unfold popAllFuel; exact List.Pairwise.nil
    · rw [ show popAllFuel ( fuel + 1 ) ( l.node x r ) = x :: popAllFuel fuel ( merge l r ) from ?_ ];
      · simp_all +decide [ List.pairwise_cons, isHeap_node_iff ];
        refine' ⟨ _, ih _ _ _ ⟩;
        · intro a' ha'
          have h_mem : a' ∈ elems (merge l r) := by
            have := popAllFuel_perm fuel ( merge l r ) ( by rw [ size_merge ] ; linarith ) ; exact this.subset ha';
          have h_mem : a' ∈ elems l ++ elems r := by
            have := elems_merge l r; exact this.subset h_mem;
          rw [List.mem_append] at h_mem
          rcases h_mem with h | h
          · exact hh.1 a' h
          · exact hh.2.1 a' h
        · rw [ size_merge ] ; linarith;
        · exact merge_isHeap hh.2.2.1 hh.2.2.2;
      · rw [ popAllFuel ]

/-- **Given**: popping a heap yields a decreasing list. Played
(re-derived) in the "Heap Sort Correctness" level; supplied here so
`heapSort_sorted` can cite it. -/
theorem popAll_sorted (h : Heap) (hh : IsHeap h) : (popAll h).Pairwise (· ≥ ·) :=
  popAllFuel_sorted (size h) h le_rfl hh

/-- **Heapsort**: build a heap, pop the maxima (giving a decreasing list),
and reverse to ascending. -/
def heapSort (l : List ℕ) : List ℕ := (popAll (buildHeap l)).reverse

/-- **Given**: heapsort returns a permutation of its input. Needed by
`heapSort_agrees_with_mergeSort`. -/
theorem heapSort_perm (l : List ℕ) : heapSort l ~ l := by
  exact List.Perm.trans ( List.reverse_perm _ ) ( List.Perm.trans ( popAll_perm _ ) ( elems_buildHeap _ ) )

/-- **Given**: heapsort returns a non-decreasing list. Played (re-derived)
in the "Heap Sort Correctness" level; supplied here so
`heapSort_agrees_with_mergeSort` can cite it. -/
theorem heapSort_sorted (l : List ℕ) : (heapSort l).Pairwise (· ≤ ·) := by
  exact List.pairwise_reverse.mpr ( popAll_sorted _ ( buildHeap_isHeap _ ) )

/-- **Given**: equivalence in results — heapsort produces exactly the same
list as merge sort. Played (re-derived) in the "Heap Sort Correctness" level;
supplied here in case a later world needs it. -/
theorem heapSort_agrees_with_mergeSort (l : List ℕ) :
    heapSort l = (mergeSortT l).ret := by
  refine sorted_perm_unique (heapSort_sorted l) (mergeSortT_sorted l) ?_
  exact (heapSort_perm l).trans (mergeSortT_perm l).symm

/-! ## Lab 16 — amortized analysis (the binary counter) -/

section Framework
variable {S : Type*}

/-- The state after performing the operation `next` a total of `n` times,
starting from `s`. -/
def stateAfter (next : S → S) : ℕ → S → S
  | 0, s => s
  | n + 1, s => stateAfter next n (next s)

/-- The total *actual* cost of performing `next` a total of `n` times,
starting from `s`. -/
def totalCost (next : S → S) (cost : S → ℕ) : ℕ → S → ℕ
  | 0, _ => 0
  | n + 1, s => cost s + totalCost next cost n (next s)

@[simp] theorem stateAfter_zero (next : S → S) (s : S) : stateAfter next 0 s = s := rfl
@[simp] theorem totalCost_zero (next : S → S) (cost : S → ℕ) (s : S) :
    totalCost next cost 0 s = 0 := rfl

/-- **Given** (Demo). **Potential method, telescoped form.** If each
operation has amortized cost `≤ c`, then after `n` operations the
accumulated actual cost *plus* the current potential is at most `c · n`
more than the starting potential. Demonstrated, not played; supplied
here so `potential_method_le` can cite it. -/
theorem potential_method (next : S → S) (cost Phi : S → ℕ) (c : ℕ)
    (h : ∀ s, cost s + Phi (next s) ≤ c + Phi s) :
    ∀ n s, totalCost next cost n s + Phi (stateAfter next n s) ≤ c * n + Phi s := by
  intro n
  induction n with
  | zero => intro s; simp only [totalCost_zero, stateAfter_zero, zero_add, mul_zero, le_refl]
  | succ n ih =>
    intro s
    have hih := ih (next s)
    have hh := h s
    simp only [totalCost, stateAfter, Nat.mul_succ]
    omega

/-- **Given**: potential method, usable form — because the potential is
non-negative, the total actual cost of `n` operations is at most `c · n`
plus the initial potential. Played (re-derived) in the "Telescoping
Potential" level; supplied here so `binaryCounter_potential` can cite
it. -/
theorem potential_method_le (next : S → S) (cost Phi : S → ℕ) (c : ℕ)
    (h : ∀ s, cost s + Phi (next s) ≤ c + Phi s) (n : ℕ) (s : S) :
    totalCost next cost n s ≤ c * n + Phi s := by
  have := potential_method next cost Phi c h n s
  omega

end Framework

/-- One increment of a binary counter (bits least-significant-first),
implemented in the `TimeM ℕ` cost monad. Each `TimeM.tick` charges one
unit for writing a bit. -/
def incrementT : List Bool → TimeM ℕ (List Bool)
  | [] => do TimeM.tick 1; pure [true]
  | false :: bs => do TimeM.tick 1; pure (true :: bs)
  | true :: bs => do
      TimeM.tick 1
      let bs' ← incrementT bs
      pure (false :: bs')

/-- The pure result of an increment: the counter after adding one. -/
def increment (bs : List Bool) : List Bool := (incrementT bs).ret

/-- The actual cost (number of bits written) of a single increment. -/
def incCost (bs : List Bool) : ℕ := (incrementT bs).time

/-- `increment []` grows a new high bit: `[] ↦ [true]`. -/
@[simp] theorem increment_nil : increment [] = [true] := by simp [increment, incrementT]
/-- A low `0` bit is simply flipped to `1`. -/
@[simp] theorem increment_false (bs) : increment (false :: bs) = true :: bs := by
  simp only [increment, incrementT, bind_pure_comp, TimeM.ret_map]
/-- A low `1` bit is reset to `0` and the carry recurses into the higher bits. -/
@[simp] theorem increment_true (bs) : increment (true :: bs) = false :: increment bs := by
  simp only [increment, incrementT, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map]

/-- Growing a new high bit costs one unit. -/
@[simp] theorem incCost_nil : incCost [] = 1 := by simp [incCost, incrementT]
/-- Flipping a low `0` bit costs one unit. -/
@[simp] theorem incCost_false (bs) : incCost (false :: bs) = 1 := by simp [incCost, incrementT]
/-- Resetting a low `1` bit costs one unit, plus the recursive carry cost. -/
@[simp] theorem incCost_true (bs) : incCost (true :: bs) = 1 + incCost bs := by
  simp only [incCost, incrementT, bind_pure_comp, TimeM.time_bind, TimeM.time_tick, TimeM.time_map]

/-- The potential of a counter: the number of set bits. -/
def Phi (bs : List Bool) : ℕ := bs.count true

/-- The empty counter has no set bits. -/
@[simp] theorem Phi_nil : Phi [] = 0 := rfl
/-- A leading `1` bit adds one to the set-bit count. -/
@[simp] theorem Phi_true (bs) : Phi (true :: bs) = Phi bs + 1 := by simp [Phi]
/-- A leading `0` bit doesn't change the set-bit count. -/
@[simp] theorem Phi_false (bs) : Phi (false :: bs) = Phi bs := by simp [Phi]

/-- **Given**: the key amortized bound — the actual cost of an increment
plus the increase in the number of set bits is at most `2`, for *every*
counter state. Played (re-derived) in the "Carry Chain" level; supplied
here so `binaryCounter_potential` can cite it. -/
theorem increment_amortized (bs : List Bool) : incCost bs + Phi (increment bs) ≤ 2 + Phi bs := by
  induction bs with
  | nil => simp only [incCost_nil, increment_nil, Phi_true, Phi_nil, zero_add, Nat.reduceAdd, add_zero, le_refl]
  | cons b bs ih =>
    cases b with
    | false => simp only [incCost_false, increment_false, Phi_true, Phi_false]; omega
    | true => simp only [incCost_true, increment_true, Phi_false, Phi_true]; omega

/-- **Given**: binary counter, via the potential method — starting from
the all-zero counter, any sequence of `n` increments costs at most `2n`
bit-writes in total. Played (re-derived) in the "Counter Bound" level;
supplied here in case a later world needs it. -/
theorem binaryCounter_potential (n : ℕ) : totalCost increment incCost n [] ≤ 2 * n := by
  have := potential_method_le increment incCost Phi 2 increment_amortized n []
  simpa only [ge_iff_le, Phi_nil, add_zero] using this

/-! ## Lab 17 — more amortized analysis (backup stack, dynamic array) -/

section SeqFramework
variable {S Op : Type*}

/-- The state after performing the list of operations `ops` in order,
starting from `s`. -/
def stateAfterL (step : Op → S → S) : List Op → S → S
  | [], s => s
  | op :: rest, s => stateAfterL step rest (step op s)

/-- The total *actual* cost of performing the operations `ops` in order,
starting from `s`. -/
def totalCostL (step : Op → S → S) (cost : Op → S → ℕ) : List Op → S → ℕ
  | [], _ => 0
  | op :: rest, s => cost op s + totalCostL step cost rest (step op s)

@[simp] theorem stateAfterL_nil (step : Op → S → S) (s : S) : stateAfterL step [] s = s := rfl
@[simp] theorem stateAfterL_cons (step : Op → S → S) (op : Op) (rest : List Op) (s : S) :
    stateAfterL step (op :: rest) s = stateAfterL step rest (step op s) := rfl
@[simp] theorem totalCostL_nil (step : Op → S → S) (cost : Op → S → ℕ) (s : S) :
    totalCostL step cost [] s = 0 := rfl
@[simp] theorem totalCostL_cons (step : Op → S → S) (cost : Op → S → ℕ)
    (op : Op) (rest : List Op) (s : S) :
    totalCostL step cost (op :: rest) s = cost op s + totalCostL step cost rest (step op s) := rfl

/-- **Given** (Demo). Potential method for a sequence of operations,
telescoped form — the list-of-operations analogue of `potential_method`,
now with a data-structure invariant `Inv` the operations must preserve.
Supplied here so `potential_method_seq_le` can cite it. -/
theorem potential_method_seq (step : Op → S → S) (cost : Op → S → ℕ) (Phi : S → ℕ) (c : ℕ)
    (Inv : S → Prop) (hpres : ∀ op s, Inv s → Inv (step op s))
    (h : ∀ op s, Inv s → cost op s + Phi (step op s) ≤ c + Phi s) :
    ∀ (ops : List Op) (s : S), Inv s →
      totalCostL step cost ops s + Phi (stateAfterL step ops s) ≤ c * ops.length + Phi s := by
  intro ops s hs; induction' ops with op ops ih generalizing s <;> simp_all +decide [ List.length_cons, Nat.mul_succ ] ;
  have hih := ih (step op s) (hpres op s hs)
  have hh := h op s hs
  omega

/-- **Given**: potential method for a sequence, usable form. Played
(re-derived) in the "Sequence Framework" level; supplied here so
`backupStack_amortized` can cite it. -/
theorem potential_method_seq_le (step : Op → S → S) (cost : Op → S → ℕ) (Phi : S → ℕ) (c : ℕ)
    (Inv : S → Prop) (hpres : ∀ op s, Inv s → Inv (step op s))
    (h : ∀ op s, Inv s → cost op s + Phi (step op s) ≤ c + Phi s)
    (ops : List Op) (s : S) (hs : Inv s) :
    totalCostL step cost ops s ≤ c * ops.length + Phi s := by
  convert potential_method_seq step cost Phi c Inv hpres h ops s hs |> le_trans _;
  exact Nat.le_add_right _ _

/-- **Given** (not played — the banker's method is the abstract dual of
the potential method over `ℤ` credits; supplied whole since no Clockwork
 level plays it directly, but `dynArray_amortized` needs it). -/
theorem bankers_method_seq (step : Op → S → S) (cost : Op → S → ℕ) (bal : S → ℤ) (c : ℕ)
    (Inv : S → Prop) (hpres : ∀ op s, Inv s → Inv (step op s))
    (h : ∀ op s, Inv s → (cost op s : ℤ) + bal (step op s) ≤ (c : ℤ) + bal s) :
    ∀ (ops : List Op) (s : S), Inv s →
      (totalCostL step cost ops s : ℤ) + bal (stateAfterL step ops s)
        ≤ (c : ℤ) * ops.length + bal s := by
  intro ops s hs;
  induction' ops with op ops ih generalizing s <;> simp_all +decide [ List.length ];
  linarith [ h op s hs, ih ( step op s ) ( hpres op s hs ) ]

/-- **Given**: banker's method for a sequence, usable form. Needed by
`dynArray_amortized`. -/
theorem bankers_method_seq_le (step : Op → S → S) (cost : Op → S → ℕ) (bal : S → ℤ) (c : ℕ)
    (Inv : S → Prop) (hpres : ∀ op s, Inv s → Inv (step op s))
    (hnn : ∀ s, Inv s → 0 ≤ bal s)
    (h : ∀ op s, Inv s → (cost op s : ℤ) + bal (step op s) ≤ (c : ℤ) + bal s)
    (ops : List Op) (s : S) (hs : Inv s) :
    (totalCostL step cost ops s : ℤ) ≤ (c : ℤ) * ops.length + bal s := by
  convert bankers_method_seq step cost bal c Inv hpres h ops s hs |> le_trans _;
  induction' ops with op ops ih generalizing s <;> simp_all +decide [ stateAfterL ]

end SeqFramework

section BackupStack
variable {α : Type*}

/-- The operations of a backup stack: `push`, `pop`, and `backup k`
("multipop" — drop the top `k` elements). -/
inductive BStackOp (α : Type*) where
  /-- Push one element onto the stack. -/
  | push (x : α)
  /-- Remove the top element, if any. -/
  | pop
  /-- Remove the top `k` elements ("back up" `k` steps). -/
  | backup (k : ℕ)

/-- Transition function of the backup stack. -/
def bStep : BStackOp α → List α → List α
  | .push x, s => x :: s
  | .pop, s => s.tail
  | .backup k, s => s.drop k

/-- Actual cost of a backup-stack operation. -/
def bCost : BStackOp α → List α → ℕ
  | .push _, _ => 1
  | .pop, _ => 1
  | .backup k, s => min k s.length

/-- The potential of a backup stack: its size (number of elements). -/
def bPhi (s : List α) : ℕ := s.length

/-- **Given**: the key amortized bound — on every stack state, the actual
cost of any operation plus the increase in size is at most `2`. Played
(re-derived) in the "Backup Stack" level; supplied here so
`backupStack_amortized` can cite it. -/
theorem bStackOp_amortized (op : BStackOp α) (s : List α) :
    bCost op s + bPhi (bStep op s) ≤ 2 + bPhi s := by
  cases op <;> simp +arith +decide [ bCost, bStep, bPhi ];
  omega

/-- **Given**: backup stack, amortized `O(1)` — any sequence of `n`
operations from the empty stack costs at most `2n` in total, even though
a single `backup` can cost up to `n`. Played (re-derived) in the "Backup
Stack" level; supplied here in case a later world needs it. -/
theorem backupStack_amortized (ops : List (BStackOp α)) :
    totalCostL bStep bCost ops ([] : List α) ≤ 2 * ops.length := by
  convert potential_method_seq_le _ _ bPhi _ _ _ _ _ _ _ using 1;
  exacts [ fun _ => True, fun _ _ _ => trivial, fun _ _ _ => bStackOp_amortized _ _, trivial ]

end BackupStack

section DynArray
variable {α : Type*}

/-- A resizable array: its `elems` (logical contents) and its physical
`cap`acity. -/
structure DynArray (α : Type*) where
  /-- The logical contents of the array. -/
  elems : List α
  /-- The physical capacity currently allocated. -/
  cap : ℕ

namespace DynArray

/-- The number of elements currently stored. -/
def size (s : DynArray α) : ℕ := s.elems.length

/-- The empty dynamic array (no elements, no capacity). -/
def empty : DynArray α := ⟨[], 0⟩

/-- Append one element, doubling the capacity first if the array is
full. -/
def append (x : α) (s : DynArray α) : DynArray α :=
  if s.size < s.cap then ⟨s.elems ++ [x], s.cap⟩
  else ⟨s.elems ++ [x], max 1 (2 * s.cap)⟩

/-- The actual cost of an append: `1` if there is room, else `size + 1`
(copy then write). -/
def appendCost (_x : α) (s : DynArray α) : ℕ :=
  if s.size < s.cap then 1 else s.size + 1

/-- Well-formedness invariant: never over capacity, and capacity at most
twice the size (so the banker's balance stays non-negative). -/
def Inv (s : DynArray α) : Prop := s.size ≤ s.cap ∧ s.cap ≤ 2 * s.size

/-- The banker's balance: `2·size − capacity`. -/
def bal (s : DynArray α) : ℤ := 2 * (s.size : ℤ) - (s.cap : ℤ)

/-- Appending one element always increases the logical size by exactly
one, whether or not it triggers a resize. -/
@[simp] theorem size_append (x : α) (s : DynArray α) : (append x s).size = s.size + 1 := by
  unfold DynArray.append;
  split_ifs <;> simp +decide [ *, DynArray.size ]

/-- **Given**: the empty array is well-formed. Needed by
`dynArray_amortized`. -/
theorem Inv_empty : Inv (empty : DynArray α) := by
  constructor <;> rfl

/-- **Given**: append preserves well-formedness. Played (re-derived) in
the "Dynamic Array" level; supplied here so `daStep_preserves_Inv` can
cite it. -/
theorem Inv_append (x : α) (s : DynArray α) (hs : Inv s) : Inv (append x s) := by
  obtain ⟨h1, h2⟩ := hs
  have hsz : (append x s).size = s.size + 1 := size_append x s
  refine ⟨?_, ?_⟩ <;> rw [hsz] <;> unfold append <;> split_ifs with hlt <;> simp only [] <;> omega

/-- **Given**: the banker's balance is always non-negative on well-formed
states. Needed by `dynArray_amortized`. -/
theorem bal_nonneg (s : DynArray α) (hs : Inv s) : 0 ≤ bal s := by
  exact Int.sub_nonneg_of_le ( by linarith [ hs.2 ] )

/-- **Given**: the key amortized bound for a resizable array — on any
well-formed state, the actual cost of an append plus the change in
balance is at most `3`. Played (re-derived) in the "Dynamic Array" level;
supplied here so `dynArray_amortized` can cite it. -/
theorem append_amortized (x : α) (s : DynArray α) (hs : Inv s) :
    (appendCost x s : ℤ) + bal (append x s) ≤ 3 + bal s := by
  obtain ⟨h1, h2⟩ := hs
  have hsz : (append x s).size = s.size + 1 := size_append x s
  unfold appendCost bal
  rw [hsz]
  unfold append
  split_ifs with hlt <;> simp only [] <;> push_cast <;> omega

end DynArray

/-- The operations of a resizable array: `append` and `lookup`. -/
inductive DAOp (α : Type*) where
  /-- Append one element. -/
  | append (x : α)
  /-- Read the element at index `i` (cost `O(1)`, state unchanged). -/
  | lookup (i : ℕ)

/-- Transition function of the resizable array. `lookup` does not change
the state. -/
def daStep : DAOp α → DynArray α → DynArray α
  | .append x, s => DynArray.append x s
  | .lookup _, s => s

/-- Actual cost of a resizable-array operation. `lookup` is `O(1)`. -/
def daCost : DAOp α → DynArray α → ℕ
  | .append x, s => DynArray.appendCost x s
  | .lookup _, _ => 1

/-- **Given**: every resizable-array operation preserves well-formedness.
Needed by `dynArray_amortized`. -/
theorem daStep_preserves_Inv (op : DAOp α) (s : DynArray α) (hs : DynArray.Inv s) :
    DynArray.Inv (daStep op s) := by
      cases op <;> simp [daStep, DynArray.Inv_append, hs]

/-- **Given**: resizable array, amortized `O(1)` — any sequence of `n`
`append`/`lookup` operations from the empty array costs at most `3n` in
total. Played (re-assembled) in the "Dynamic Array" level; supplied here
in case a later world needs it. -/
theorem dynArray_amortized (ops : List (DAOp α)) :
    totalCostL daStep daCost ops (DynArray.empty : DynArray α) ≤ 3 * ops.length := by
  have h_bankers : ∀ (ops : List (DAOp α)) (s : DynArray α) (hs : DynArray.Inv s), (totalCostL daStep daCost ops s : ℤ) ≤ 3 * ops.length + DynArray.bal s := by
    intros ops s hs;
    convert bankers_method_seq_le daStep daCost DynArray.bal 3 DynArray.Inv daStep_preserves_Inv ( fun s hs => DynArray.bal_nonneg s hs ) ( fun op s hs => ?_ ) ops s hs using 1;
    cases op <;> simp +decide [ * ];
    · convert DynArray.append_amortized _ _ hs using 1;
    · simp +decide [ daCost, daStep ];
  exact_mod_cast h_bankers ops DynArray.empty DynArray.Inv_empty |> le_trans <| add_le_of_nonpos_right <| by simp +decide [ DynArray.bal ] ;

end DynArray

/-- Insert `x` into its ordered position in a list. -/
def insert (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

/-- Compatibility name for earlier insertion-sort levels. -/
def insertIS (x : ℕ) : List ℕ → List ℕ := insert x

/-- Functional insertion sort, in the usual two-function Haskell style. -/
def insertionSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => insert x (insertionSort xs)

/-- The number of comparisons `insert x s` performs: it inspects the list from
the front, charging one comparison per element until it finds the insertion
point or runs out of list. -/
def insertCost (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: ys => 1 + (if x ≤ y then 0 else insertCost x ys)

/-- The total number of comparisons `insertionSort` performs. -/
def insertionSortCost : List ℕ → ℕ
  | [] => 0
  | x :: xs => insertionSortCost xs + insertCost x (insertionSort xs)

end Game.Clockwork
