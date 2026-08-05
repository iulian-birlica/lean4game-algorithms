import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Recurrence"
Level 2
Title "Master Cases"
-- source: RequestProject Lab11.masterSeq_case1, Lab11.masterSeq_case2

Introduction "**The Master Theorem, cases 1 and 2.** Case 1: if the toll
`Fₖ` is dominated by the critical term (`Fₖ ≤ M·aᵏ·cᵏ` for `c < 1`), the
recurrence is `Θ(aᵏ)`. Case 2: if the toll is comparable to the critical
term (`c₁·aᵏ ≤ Fₖ ≤ c₂·aᵏ`), the recurrence is `Θ(aᵏ·k)`. Assemble both
from the supplied recursion-tree estimates."

Statement {a d : ℝ} (ha : 1 ≤ a) (hd : 0 < d)
    {F₁ : ℕ → ℝ} (hF₁ : ∀ k, 0 ≤ F₁ k) {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 < M)
    (hbound : ∀ k, 1 ≤ k → F₁ k ≤ M * a ^ k * c ^ k)
    {F₂ : ℕ → ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlb : ∀ k, 1 ≤ k → c₁ * a ^ k ≤ F₂ k) (hub : ∀ k, 1 ≤ k → F₂ k ≤ c₂ * a ^ k) :
    masterSeq a d F₁ =Θ (fun k => a ^ k) ∧
      masterSeq a d F₂ =Θ (fun k => a ^ k * (k : ℝ)) := by
  Hint "Prove the two cases separately; each is a `=Θ` pair (upper and lower
  bound), built from the supplied recursion-tree sum estimates."
  constructor
  · Hint (hidden := true) "Case 1's upper bound uses `masterSeq_case1_sum_upper`; the lower
    bound is immediate from nonnegativity of the toll."
    constructor
    · use d + M * (1 - c)⁻¹
      refine' ⟨by nlinarith [inv_pos.mpr (by linarith : 0 < 1 - c)], 0, fun n hn => _⟩
      rw [abs_of_nonneg, abs_of_nonneg]
      · have := masterSeq_case1_sum_upper ha hM hc0 hc1 hbound n
        rw [masterSeq_closed]; nlinarith [pow_pos (zero_lt_one.trans_le ha) n]
      · positivity
      · induction' n with n ih
        · exact hd.le
        · exact add_nonneg (mul_nonneg (by positivity) (ih (Nat.zero_le _))) (hF₁ _)
    · use 1 / d
      refine' ⟨by positivity, 0, fun n hn => _⟩
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by exact masterSeq_closed a d F₁ n ▸ add_nonneg (mul_nonneg (pow_nonneg (by positivity) _) hd.le) (Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (by positivity) _) (hF₁ _)))]
      rw [div_mul_eq_mul_div, le_div_iff₀] <;> nlinarith [show 0 ≤ ∑ i ∈ Finset.range n, a ^ i * F₁ (n - i) from Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (by linarith) _) (hF₁ _), show 0 ≤ a ^ n * d from mul_nonneg (pow_nonneg (by linarith) _) hd.le, masterSeq_closed a d F₁ n]
  · Hint (hidden := true) "Case 2's upper bound uses `masterSeq_case2_sum_upper`; the lower
    bound uses `masterSeq_case2_sum_lower`. Both rely on
    `masterSeq_nonneg_of_case2_lower` for nonnegativity."
    constructor
    · use c₂ + d, by positivity, 1
      intro n hn
      rw [abs_of_nonneg (masterSeq_nonneg_of_case2_lower ha hd hc₁ hlb n)]
      rw [abs_of_nonneg (by positivity)]
      rw [masterSeq_closed]; ring_nf
      have := masterSeq_case2_sum_upper ha hub n
      nlinarith [show (n : ℝ) ≥ 1 by norm_cast, show (a ^ n : ℝ) * d ≥ 0 by positivity,
        show (a ^ n : ℝ) * c₂ ≥ 0 by positivity, show (n : ℝ) * a ^ n * d ≥ 0 by positivity,
        show (n : ℝ) * a ^ n * c₂ ≥ 0 by positivity]
    · use 1 / c₁
      refine' ⟨by positivity, 1, fun n hn => _⟩
      rw [abs_of_nonneg (by positivity),
        abs_of_nonneg (by exact masterSeq_nonneg_of_case2_lower ha hd hc₁ hlb n)]
      rw [masterSeq_closed]
      rw [div_mul_eq_mul_div, le_div_iff₀] <;> nlinarith [masterSeq_case2_sum_lower ha hlb n,
        show 0 ≤ a ^ n * d by positivity,
        show 0 ≤ ∑ i ∈ Finset.range n, a ^ i * F₂ (n - i) by exact Finset.sum_nonneg fun i hi => mul_nonneg (pow_nonneg (by positivity) _) (by exact le_trans (by positivity) (hlb _ (Nat.sub_pos_of_lt (Finset.mem_range.mp hi))))]

Conclusion "Verified: the Master Theorem's first two cases, proved in full."

NewTactic ring_nf
NewDefinition Game.Clockwork.IsBigTheta Finset.range
NewTheorem Game.Clockwork.masterSeq_closed Game.Clockwork.masterSeq_case1_sum_upper
  Game.Clockwork.masterSeq_case2_sum_upper Game.Clockwork.masterSeq_case2_sum_lower
  Game.Clockwork.masterSeq_nonneg_of_case2_lower
  inv_pos zero_lt_one add_nonneg mul_nonneg pow_nonneg pow_pos Finset.sum_nonneg
  Nat.sub_pos_of_lt
