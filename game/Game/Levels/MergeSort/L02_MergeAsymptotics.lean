import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "MergeSort"
Level 2
Title "Merge Asymptotics"
-- source: RequestProject Lab12.mstime_pow, Lab12.mstime_isBigTheta_nlogn

Introduction "**Merge sort is `Θ(n log n)`.** First pin down the exact
value on powers of two, then classify the whole cost function using the
supplied logarithm bounds."

Statement (k : ℕ) :
    mstime (2 ^ k) = k * 2 ^ k ∧
      (fun n => (mstime n : ℝ)) =Θ (fun n => (n : ℝ) * Real.log n) := by
  Hint "Prove the exact power-of-two value first, by induction on `k`, then
  assemble the `=Θ` classification from `mstime_le`/`mstime_ge` and the
  supplied logarithm bounds."
  constructor
  · induction' k with k ih
    · native_decide +revert
    · convert mstime_rec (show 2 ≤ 2 ^ (k + 1) from ?_) using 1
      · have hp : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        have e1 : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [hp]; omega
        have e2 : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by rw [hp]; omega
        rw [e1, e2, ih]; simp only [hp]; ring
      · exact le_self_pow (by norm_num) (by norm_num)
  · Hint (hidden := true) "Both halves of `=Θ` reduce to `norm_num [IsBigO, IsLittleO]`
    followed by a witness constant and heavy `nlinarith`/`positivity` bookkeeping."
    constructor <;> norm_num [IsBigO, IsLittleO]
    · refine' ⟨2 / Real.log 2, by positivity, 2, fun n hn => _⟩
      have h_mstime_le : (mstime n : ℝ) ≤ n * (Nat.log 2 n + 1) := by
        exact_mod_cast le_trans (mstime_le n) (by nlinarith [clog_le_log_succ n])
      have h_log_le : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
        rw [le_div_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
        exact Real.log_le_log (by positivity) (mod_cast Nat.pow_log_le_self _ <| by positivity)
      rw [abs_of_nonneg (Real.log_nonneg (by norm_cast; linarith))]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at *
      nlinarith [show (n : ℝ) ≥ 2 by norm_cast, show (Nat.log 2 n : ℝ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le (by norm_num) hn, Real.log_pos one_lt_two, mul_le_mul_of_nonneg_left (show (Real.log 2 : ℝ) ≥ 1 / 2 by exact Real.log_two_gt_d9.le.trans' <| by norm_num) <| Nat.cast_nonneg n]
    · refine' ⟨2 * Real.exp 1, by positivity, 2, fun n hn => _⟩
      rw [abs_of_nonneg (Real.log_nonneg (by norm_cast; linarith))]
      have h_log_lt_natLog_succ : Real.log n < (Nat.log 2 n + 1) * Real.log 2 := by
        convert log_lt_natLog_succ hn using 1
      have h_mstime_ge : (mstime n : ℝ) ≥ n * Nat.log 2 n := by exact_mod_cast mstime_ge n
      have h_log2_le_exp1 : Real.log 2 ≤ Real.exp 1 / 2 := by
        exact le_trans (Real.log_two_lt_d9.le) (by norm_num; have := Real.exp_one_gt_d9.le; norm_num1 at *; linarith)
      nlinarith [Real.add_one_le_exp 1, show (n : ℝ) ≥ 2 by norm_cast, show (Nat.log 2 n : ℝ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith), mul_le_mul_of_nonneg_left (show (Nat.log 2 n : ℝ) ≥ 1 by exact_mod_cast Nat.le_log_of_pow_le (by norm_num) (by linarith)) (show (0 : ℝ) ≤ n by positivity)]

Conclusion "Verified: merge sort's running time is provably `Θ(n log n)`."

NewDefinition Game.Clockwork.mstime Game.Clockwork.IsLittleO Nat.log Real.log Real.exp
NewTactic convert norm_num1 exact_mod_cast «mod_cast»
NewTheorem Game.Clockwork.mstime_rec Game.Clockwork.mstime_le
  Game.Clockwork.mstime_ge Game.Clockwork.clog_le_log_succ
  Game.Clockwork.log_lt_natLog_succ le_self_pow Real.log_pos Real.log_le_log
  Real.log_nonneg Real.log_two_gt_d9 Real.log_two_lt_d9 Real.exp_one_gt_d9 Real.add_one_le_exp
  Nat.le_log_of_pow_le Nat.pow_log_le_self one_lt_two Real.log_pow Nat.cast_nonneg
