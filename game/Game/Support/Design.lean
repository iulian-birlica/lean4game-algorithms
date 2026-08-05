import Mathlib

/-! Answer-free definitions and given (already-proven) facts used by the design
worlds. Ported from `RequestProject/Lab05GreedyAlgorithms.lean`
(continuous knapsack) and `RequestProject/Lab06DynamicProgramming.lean` (0/1
knapsack and coin change). As with the Contracts world, theorems here are
either prerequisites a level's proof is allowed to cite, or genuinely
out-of-scope infrastructure — the level files still perform the exchange
argument or DP-recurrence proof the lab teaches. No level solutions live
here. -/
namespace Game.Design

open scoped BigOperators

/-! ## Lab 05 — the continuous (fractional) knapsack: a greedy algorithm -/

/-- A single material: `w` is the available weight, `v` is its total value. -/
structure Item where
  /-- The available weight of the material. -/
  w : ℝ
  /-- The total value of the material. -/
  v : ℝ

/-- All materials have strictly positive weight. -/
def PosWeights (items : List Item) : Prop := ∀ it ∈ items, 0 < it.w

/-- All materials have non-negative value. -/
def NonnegValues (items : List Item) : Prop := ∀ it ∈ items, 0 ≤ it.v

/-- The materials are sorted by decreasing value density `v / w`, written in
cross-multiplied form `b.v * a.w ≤ a.v * b.w` to avoid dividing. -/
def SortedByDensity (items : List Item) : Prop :=
  List.Pairwise (fun a b => b.v * a.w ≤ a.v * b.w) items

/-- The weight consumed by a choice `x` of fractions: `∑ xᵢ · wᵢ`. -/
def usedWeight : List Item → List ℝ → ℝ
  | [], _ => 0
  | _ :: _, [] => 0
  | it :: its, x :: xs => x * it.w + usedWeight its xs

/-- The value obtained by a choice `x` of fractions: `∑ xᵢ · vᵢ`. -/
def totalValue : List Item → List ℝ → ℝ
  | [], _ => 0
  | _ :: _, [] => 0
  | it :: its, x :: xs => x * it.v + totalValue its xs

/-- A choice `x` is feasible for capacity `c`: one fraction per material, each
in `[0,1]`, with weight used not exceeding `c`. -/
def Feasible (items : List Item) (c : ℝ) (x : List ℝ) : Prop :=
  x.length = items.length ∧ (∀ xi ∈ x, 0 ≤ xi ∧ xi ≤ 1) ∧ usedWeight items x ≤ c

/-- The greedy value: sort by decreasing density, take as much of each
material as fits. `noncomputable` because comparisons on `ℝ` are not
computable — this is a specification/reference implementation. -/
noncomputable def greedy : List Item → ℝ → ℝ
  | [], _ => 0
  | it :: rest, c =>
      if it.w ≤ c then it.v + greedy rest (c - it.w)
      else (c / it.w) * it.v

/-- **Given**: the weight used by a choice with non-negative fractions is
non-negative. -/
theorem usedWeight_nonneg (items : List Item) (x : List ℝ)
    (hpos : PosWeights items) (hx : ∀ xi ∈ x, 0 ≤ xi) :
    0 ≤ usedWeight items x := by
  induction' items with it its ih generalizing x <;> induction' x with xi x ih' <;> simp_all +decide only [usedWeight, le_refl, List.mem_cons, or_true, implies_true, forall_eq_or_imp, forall_const];
  exact add_nonneg ( mul_nonneg hx.1 ( le_of_lt ( hpos it ( by simp +decide only [List.mem_cons, true_or] ) ) ) ) ( ih x ( fun a ha => hpos a ( by simp +decide only [List.mem_cons, ha, or_true] ) ) hx.2 )

/-- **Given**: if every material has density at most `ρ`, then for
non-negative capacity the greedy value is at most `ρ · c`. -/
theorem greedy_le_density_cap (items : List Item) (c : ℝ) (ρ : ℝ)
    (hpos : PosWeights items) (hden : ∀ it ∈ items, it.v ≤ ρ * it.w)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ c) :
    greedy items c ≤ ρ * c := by
  induction' items with it rest ih generalizing c;
  · exact mul_nonneg hρ hc;
  · by_cases h : it.w ≤ c <;> simp_all +decide only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, greedy, ↓reduceIte, not_le];
    · nlinarith [ ih ( c - it.w ) ( fun a ha => hpos a ( List.mem_cons_of_mem _ ha ) ) ( sub_nonneg.mpr h ), hpos it ( List.mem_cons_self ) ];
    · rw [ if_neg h.not_ge ];
      rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ hpos it ( by simp +decide only [List.mem_cons, true_or] ) ]

/-- **Given**: if every material has density at most `ρ`, then increasing the
capacity by `δ ≥ 0` increases the greedy value by at most `ρ · δ` — the key
exchange-argument step. -/
theorem greedy_marginal (items : List Item) (a δ ρ : ℝ)
    (hpos : PosWeights items) (hden : ∀ it ∈ items, it.v ≤ ρ * it.w)
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (ha : 0 ≤ a) :
    greedy items (a + δ) ≤ greedy items a + ρ * δ := by
  induction' items with it rest ih generalizing a;
  · exact show 0 ≤ 0 + ρ * δ by positivity;
  · by_cases hcase : it.w ≤ a;
    · rw [ show greedy ( it :: rest ) ( a + δ ) = it.v + greedy rest ( ( a + δ ) - it.w ) from ?_, show greedy ( it :: rest ) a = it.v + greedy rest ( a - it.w ) from ?_ ];
      · have := ih ( a - it.w ) ( fun it hit => hpos it ( List.mem_cons_of_mem _ hit ) ) ( fun it hit => hden it ( List.mem_cons_of_mem _ hit ) ) ( by linarith [ hpos it ( List.mem_cons_self ) ] ) ; ring_nf at *; linarith;
      · exact if_pos hcase;
      · exact if_pos ( by linarith );
    · by_cases hcase3 : it.w ≤ a + δ <;> simp_all +decide only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, not_le, greedy, ↓reduceIte];
      · split_ifs <;> try linarith;
        have := greedy_le_density_cap rest ( a + δ - it.w ) ρ ( fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) ) ( fun x hx => hden.2 x hx ) hρ ( by linarith );
        rw [ div_mul_eq_mul_div, add_comm ];
        rw [ div_add', le_div_iff₀ ] <;> nlinarith [ hpos it ( by simp +decide only [List.mem_cons, true_or] ), mul_div_cancel₀ ( a * it.v ) ( ne_of_gt ( hpos it ( by simp +decide only [List.mem_cons, true_or] ) ) ) ];
      · rw [ if_neg ( by linarith ), if_neg ( by linarith ) ];
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_add', div_le_div_iff_of_pos_right ] <;> nlinarith [ hpos it ( by simp +decide only [List.mem_cons, true_or] ) ]

/-- **Given**: greedy with zero capacity yields zero value. -/
theorem greedy_zero (items : List Item) (hpos : PosWeights items) :
    greedy items 0 = 0 := by
  induction' items with it rest ih;
  · rfl;
  · simp_all +decide only [greedy, zero_sub, zero_div, zero_mul, ite_eq_right_iff];
    exact fun h => absurd h ( not_le_of_gt ( hpos it ( by simp +decide only [List.mem_cons, true_or] ) ) )

/-- **Given**: if every material has density at most `ρ`, then any choice with
non-negative fractions obtains value at most `ρ` times the weight it uses.
Played (re-derived) in the "Density Upper Bound" level; supplied here so
`greedy_upper_bound` can cite it. -/
theorem value_le_density_weight (items : List Item) (x : List ℝ) (ρ : ℝ)
    (hden : ∀ it ∈ items, it.v ≤ ρ * it.w) (hx : ∀ xi ∈ x, 0 ≤ xi) :
    totalValue items x ≤ ρ * usedWeight items x := by
  induction items generalizing x with
  | nil => simp only [totalValue, usedWeight, mul_zero, le_refl]
  | cons it its ih =>
    cases x with
    | nil => simp only [totalValue, usedWeight, mul_zero, le_refl]
    | cons x0 xs =>
      have hx0 : 0 ≤ x0 := hx x0 (by simp only [List.mem_cons, true_or])
      have hitv : it.v ≤ ρ * it.w := hden it (by simp only [List.mem_cons, true_or])
      have hih : totalValue its xs ≤ ρ * usedWeight its xs :=
        ih xs (fun it' h => hden it' (by simp only [List.mem_cons, h, or_true])) (fun xi h => hx xi (by simp only [List.mem_cons, h, or_true]))
      have hmul : x0 * it.v ≤ x0 * (ρ * it.w) := mul_le_mul_of_nonneg_left hitv hx0
      simp only [totalValue, usedWeight]
      nlinarith [hmul, hih]

/-- **Given**: from `SortedByDensity`, every material's density is bounded by
the head's density `it.v / it.w`. Played (re-derived) in the "Exchange
Density order" level; supplied here so `greedy_upper_bound` can cite it. -/
theorem density_bound_of_sorted (it : Item) (rest : List Item)
    (hpos : PosWeights (it :: rest)) (hsorted : SortedByDensity (it :: rest)) :
    ∀ b ∈ (it :: rest), b.v ≤ (it.v / it.w) * b.w := by
  intro b hb;
  cases' hb with hb hb;
  · rw [ div_mul_cancel₀ _ ( ne_of_gt ( hpos _ ( by simp +decide only [List.mem_cons, true_or] ) ) ) ];
  · rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> linarith [ hpos it ( by tauto ), hpos b ( by tauto ), hsorted |> List.pairwise_cons.mp |>.1 b ( by tauto ) ]

/-- **Given**: optimality upper bound — every feasible choice obtains value at
most the greedy value. This is the theorem the "Greedy Optimality" boss level
assembles into `greedy_is_optimal`, using `greedy_marginal` and this result's
own dependencies (`value_le_density_weight`, `density_bound_of_sorted`, both
played in earlier levels) as its own internal machinery. -/
theorem greedy_upper_bound (items : List Item) (c : ℝ) (x : List ℝ)
    (hpos : PosWeights items) (hval : NonnegValues items)
    (hsorted : SortedByDensity items) (hfeas : Feasible items c x) :
    totalValue items x ≤ greedy items c := by
  induction' items with it rest ih generalizing c x;
  · cases x <;> norm_num [ totalValue, greedy ];
  · rcases x with ( _ | ⟨ x0, xs ⟩ ) <;> simp_all +decide only [Feasible, and_imp, List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, and_false, true_and, false_and, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp];
    unfold greedy; split_ifs <;> simp_all +decide only [usedWeight, totalValue, not_le] ;
    · have h_ind : totalValue rest xs ≤ greedy rest (c - x0 * it.w) := by
        apply ih;
        all_goals try { exact fun x hx => hpos x <| List.mem_cons_of_mem _ hx };
        · exact fun x hx => hval x <| List.mem_cons_of_mem _ hx;
        · exact hsorted.tail;
        · exact hfeas.1;
        · exact hfeas.2.1.2;
        · linarith;
      have h_marginal : greedy rest (c - x0 * it.w) ≤ greedy rest (c - it.w) + (it.v / it.w) * (it.w * (1 - x0)) := by
        have h_pos : 0 < it.w := hpos it (by simp only [List.mem_cons, true_or])
        have h_nonneg : 0 ≤ it.v / it.w := div_nonneg (hval it (by simp only [List.mem_cons, true_or])) h_pos.le
        convert greedy_marginal rest ( c - it.w ) ( it.w * ( 1 - x0 ) ) ( it.v / it.w ) ( fun it' hit' => hpos it' ( List.mem_cons_of_mem _ hit' ) ) ( fun it' hit' => density_bound_of_sorted it rest hpos hsorted it' ( List.mem_cons_of_mem _ hit' ) ) h_nonneg ( mul_nonneg h_pos.le ( sub_nonneg.mpr hfeas.2.1.1.2 ) ) ( by nlinarith ) using 2 ; ring;
      by_cases h : it.w = 0 <;> simp_all +decide only [mul_zero, zero_add, sub_zero, div_zero, zero_mul, add_zero, le_refl, ge_iff_le, div_mul_eq_mul_div];
      · exact absurd h ( ne_of_gt ( hpos it ( by simp +decide only [List.mem_cons, true_or] ) ) );
      · rw [ mul_div_assoc, mul_div_cancel_left₀ _ h ] at h_marginal ; linarith;
    · have h_value_le_density_weight : totalValue (it :: rest) (x0 :: xs) ≤ (it.v / it.w) * (x0 * it.w + usedWeight rest xs) := by
        convert value_le_density_weight ( it :: rest ) ( x0 :: xs ) ( it.v / it.w ) _ _ using 1;
        · exact fun b hb => density_bound_of_sorted it rest hpos hsorted b hb;
        · intro xi hxi
          rcases List.mem_cons.mp hxi with rfl | h
          · exact hfeas.2.1.1.1
          · exact (hfeas.2.1.2 xi h).1;
      convert h_value_le_density_weight.trans ( mul_le_mul_of_nonneg_left hfeas.2.2 ( div_nonneg ( hval it ( by simp +decide only [List.mem_cons, true_or] ) ) ( le_of_lt ( hpos it ( by simp +decide only [List.mem_cons, true_or] ) ) ) ) ) using 1 ; ring

/-- The choice vector realised by the greedy strategy. -/
noncomputable def greedyAssign : List Item → ℝ → List ℝ
  | [], _ => []
  | it :: rest, c =>
      if it.w ≤ c then 1 :: greedyAssign rest (c - it.w)
      else (c / it.w) :: greedyAssign rest 0

/-- **Given**: the greedy choice has one fraction per material. -/
theorem greedyAssign_length (items : List Item) (c : ℝ) :
    (greedyAssign items c).length = items.length := by
  induction items generalizing c with
  | nil => rfl
  | cons it rest ih =>
    unfold greedyAssign
    split_ifs <;> rw [List.length_cons, ih, List.length_cons]

/-- **Given**: the greedy choice obtains exactly the greedy value. -/
theorem greedyAssign_value (items : List Item) (c : ℝ) (hpos : PosWeights items) :
    totalValue items (greedyAssign items c) = greedy items c := by
  induction' items with it rest ih generalizing c;
  · rfl;
  · unfold greedyAssign greedy;
    split_ifs <;> simp_all +decide only [totalValue, one_mul, add_right_inj, not_le, add_eq_left];
    · exact ih _ fun x hx => hpos x <| List.mem_cons_of_mem _ hx;
    · convert ih 0 ( fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) ) using 1;
      exact Eq.symm ( greedy_zero _ fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) )

/-- **Given**: the greedy choice respects the capacity constraint. -/
theorem greedyAssign_used (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    usedWeight items (greedyAssign items c) ≤ c := by
  induction' items with it rest ih generalizing c;
  · exact hc;
  · by_cases h : it.w ≤ c <;> simp_all +decide only [greedyAssign, ↓reduceIte, usedWeight, one_mul, not_le];
    · linarith [ ih ( c - it.w ) ( fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) ) ( sub_nonneg.mpr h ) ];
    · have h_usedWeight_rest : usedWeight (it :: rest) ((c / it.w) :: greedyAssign rest 0) = (c / it.w) * it.w + usedWeight rest (greedyAssign rest 0) := by
        rfl;
      rw [ if_neg h.not_ge, h_usedWeight_rest, div_mul_cancel₀ _ ( by linarith ) ] ; linarith [ ih 0 ( fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) ) ( by linarith ) ]

/-- **Given**: every fraction chosen by the greedy strategy lies in `[0,1]`.
Played (re-derived) in the "Greedy Knapsack Feasibility" level; supplied here so
`greedyAssign_feasible` can cite it. -/
theorem greedyAssign_entries (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    ∀ xi ∈ greedyAssign items c, 0 ≤ xi ∧ xi ≤ 1 := by
  induction items generalizing c with
  | nil =>
    simp_all +decide only [PosWeights, List.mem_cons, forall_eq_or_imp, implies_true, forall_const]
    tauto
  | cons k rest ih =>
    simp_all +decide only [PosWeights, List.mem_cons, forall_eq_or_imp, implies_true, forall_const]
    intro xi hxi
    unfold greedyAssign at hxi
    split_ifs at hxi <;> simp_all +decide only [List.mem_cons, not_le]
    · exact hxi.elim (fun h => h.symm ▸ by norm_num) fun h => ih _ (by linarith) _ h
    · exact hxi.elim (fun h => ⟨by rw [h]; exact div_nonneg hc hpos.1.le,
        by rw [h]; exact div_le_one_of_le₀ (by linarith) hpos.1.le⟩) fun h => ih _ le_rfl _ h

/-- **Given**: the greedy choice is feasible. -/
theorem greedyAssign_feasible (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    Feasible items c (greedyAssign items c) :=
  ⟨greedyAssign_length items c,
   greedyAssign_entries items c hpos hc,
   greedyAssign_used items c hpos hc⟩

/-- Proof-carrying greedy choice: returns the greedy assignment together with
a proof that this exact list is feasible. -/
noncomputable def greedyFeasibleCarry (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    { x : List ℝ // x = greedyAssign items c ∧ Feasible items c x } :=
  ⟨greedyAssign items c, by
    exact ⟨rfl, greedyAssign_feasible items c hpos hc⟩⟩

/-- Proof-carrying greedy witness: returns a feasible choice together with a
proof that it attains the reference greedy value. -/
noncomputable def greedyWitnessCarry (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    { x : List ℝ // Feasible items c x ∧ totalValue items x = greedy items c } :=
  ⟨greedyAssign items c, by
    exact ⟨greedyAssign_feasible items c hpos hc, greedyAssign_value items c hpos⟩⟩

/-- Proof-carrying greedy: returns the value together with a proof that it
equals the reference value `greedy items c`. -/
noncomputable def greedyCarry : (items : List Item) → (c : ℝ) →
    { v : ℝ // greedy items c = v }
  | [], _ => ⟨0, by rfl⟩
  | it :: rest, c =>
      if h : it.w ≤ c then
        let r := greedyCarry rest (c - it.w)
        ⟨it.v + r.val, by rw [greedy, if_pos h]; congr 1; exact r.property⟩
      else
        ⟨(c / it.w) * it.v, by rw [greedy, if_neg h]⟩

/-- The top-level proof-carrying algorithm: just the value component. -/
noncomputable def greedyImpl (items : List Item) (c : ℝ) : ℝ :=
  (greedyCarry items c).1

/-! ## Lab 06 — dynamic programming: 0/1 knapsack and coin change -/

/-- A single item: integer weight `w` and integer value `v`. -/
structure KItem where
  /-- The integer weight of the item. -/
  w : ℕ
  /-- The integer value of the item. -/
  v : ℕ

/-- The total weight of the taken items, `∑_{i taken} wᵢ`. -/
def selWeight : List KItem → List Bool → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | it :: its, b :: bs => (if b then it.w else 0) + selWeight its bs

/-- The total value of the taken items, `∑_{i taken} vᵢ`. -/
def selValue : List KItem → List Bool → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | it :: its, b :: bs => (if b then it.v else 0) + selValue its bs

/-- A selection is feasible for capacity `c`: one bit per item, total weight
not exceeding `c`. -/
def KFeasible (items : List KItem) (c : ℕ) (s : List Bool) : Prop :=
  s.length = items.length ∧ selWeight items s ≤ c

/-- The DP recurrence for the 0/1 knapsack: skip the head, or (if it fits)
take it and recurse on the smaller capacity — whichever is larger. -/
def knap : List KItem → ℕ → ℕ
  | [], _ => 0
  | it :: rest, c =>
      if it.w ≤ c then max (knap rest c) (it.v + knap rest (c - it.w))
      else knap rest c

/-- **Given**: dropping the head item can only decrease the achievable
value. Played in the "Knapsack Recurrence" level; supplied here (and used
by `knap_upper_bound`) so later facts can build on it. -/
theorem knap_tail_le (it : KItem) (rest : List KItem) (c : ℕ) :
    knap rest c ≤ knap (it :: rest) c := by
  by_cases h : it.w ≤ c <;> simp +decide only [knap, h, ↓reduceIte, le_sup_left, le_refl]

/-- **Given**: optimality upper bound — every feasible selection obtains
value at most the DP value. Out of scope for "Knapsack Recurrence" (which
plays only `knap_tail_le`); given whole for the "Knapsack Optimality" boss
level to assemble. -/
theorem knap_upper_bound (items : List KItem) (c : ℕ) (s : List Bool)
    (hfeas : KFeasible items c s) :
    selValue items s ≤ knap items c := by
  revert s;
  induction' items with it rest ih generalizing c;
  · rintro ( _ | _ ) <;> tauto;
  · intro s hs;
    rcases s with ( _ | ⟨ b, s ⟩ ) <;> simp_all +decide only [KFeasible, and_imp, List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff, and_false, false_and, Nat.add_right_cancel_iff];
    cases b <;> simp_all +decide only [selWeight, ↓reduceIte, zero_add, selValue];
    · exact le_trans ( ih _ _ hs.1 hs.2 ) ( knap_tail_le _ _ _ );
    · rw [ show knap ( it :: rest ) c = if it.w ≤ c then max ( knap rest c ) ( it.v + knap rest ( c - it.w ) ) else knap rest c from rfl ];
      split_ifs <;> simp_all +decide only [le_sup_iff, add_le_add_iff_left, not_le];
      · exact Or.inr ( ih _ _ hs.1 ( by omega ) );
      · linarith [ Nat.zero_le ( selWeight rest s ) ]

/-- **Given**: achievability — there is a feasible selection attaining the
DP value. Given whole for the "Knapsack Optimality" boss level to
assemble. -/
theorem knap_achievable (items : List KItem) (c : ℕ) :
    ∃ s, KFeasible items c s ∧ selValue items s = knap items c := by
  induction' items with it rest ih generalizing c;
  · exists [ ];
    exact ⟨ ⟨ rfl, Nat.zero_le _ ⟩, rfl ⟩;
  · by_cases h : it.w ≤ c;
    · obtain ⟨ s1, hs1, hs1' ⟩ := ih c; obtain ⟨ s2, hs2, hs2' ⟩ := ih ( c - it.w ) ; simp_all +decide only [KFeasible, List.length_cons, knap, ↓reduceIte] ;
      cases max_cases ( knap rest c ) ( it.v + knap rest ( c - it.w ) ) <;> simp_all +decide only [sup_eq_left, and_self, sup_of_le_left, sup_eq_right, sup_of_le_right];
      · use false :: s1; simp_all +decide only [List.length_cons, selWeight, ↓reduceIte, zero_add, and_self, selValue] ;
      · use true :: s2; simp_all +decide only [List.length_cons, selWeight, ↓reduceIte, true_and, selValue, and_true] ;
        omega;
    · obtain ⟨ s, hs ⟩ := ih c;
      exact ⟨ Bool.false :: s, ⟨ by simp +decide only [List.length_cons, hs.1.1], by simp +decide only [selWeight, ↓reduceIte, zero_add, hs.1.2] ⟩, by simp +decide only [selValue, ↓reduceIte, hs.2, zero_add, knap, h] ⟩

/-- Proof-carrying knapsack: returns the value together with a proof that it
equals the reference value `knap items c`. -/
def knapCarry : (items : List KItem) → (c : ℕ) → { v : ℕ // knap items c = v }
  | [], _ => ⟨0, rfl⟩
  | it :: rest, c =>
      if h : it.w ≤ c then
        let r1 := knapCarry rest c
        let r2 := knapCarry rest (c - it.w)
        ⟨max r1.val (it.v + r2.val), by
          rw [knap, if_pos h]
          exact congr_arg₂ max r1.property (congr_arg (it.v + ·) r2.property)⟩
      else
        let r1 := knapCarry rest c
        ⟨r1.val, by rw [knap, if_neg h]; exact r1.property⟩

/-- The top-level proof-carrying algorithm: just the value component. -/
def knapImpl (items : List KItem) (c : ℕ) : ℕ := (knapCarry items c).1

/-- **Given**: the DP recurrence solves the 0/1 knapsack — the assembled
achievability/optimality contract. Played (re-assembled) in the "Knapsack
Optimality" boss level; supplied here so "Certified Knapsack" can transfer
it to the proof-carrying implementation. -/
theorem knap_is_optimal (items : List KItem) (c : ℕ) :
    (∃ s, KFeasible items c s ∧ selValue items s = knap items c) ∧
    (∀ s, KFeasible items c s → selValue items s ≤ knap items c) :=
  ⟨knap_achievable items c, fun s hs => knap_upper_bound items c s hs⟩

/-- Every denomination is a positive amount of money. -/
def PosCoins (coins : List ℕ) : Prop := ∀ c ∈ coins, 0 < c

/-- A representation of `amount` using `coins` is a list of coins, each drawn
from `coins`, summing to `amount`. -/
def IsRep (coins : List ℕ) (amount : ℕ) (r : List ℕ) : Prop :=
  (∀ x ∈ r, x ∈ coins) ∧ r.sum = amount

/-- Computable binary minimum on `ℕ∞` (the `CompleteLinearOrder` `min` is
noncomputable, so we spell it out; it agrees with `min`). -/
def cmin (a b : ℕ∞) : ℕ∞ := if a ≤ b then a else b

/-- The DP recurrence for coin change, in the two-dimensional form
`minCoins coins amount`: either skip denomination `c`, or use one `c` and
recurse on the same denominations at the reduced amount — keep whichever
needs fewer coins. -/
def minCoins : List ℕ → ℕ → ℕ∞
  | [], 0 => 0
  | [], _ + 1 => ⊤
  | c :: cs, amount =>
      cmin (minCoins cs amount)
        (if 0 < c ∧ c ≤ amount then minCoins (c :: cs) (amount - c) + 1 else ⊤)
termination_by coins amount => (coins.length, amount)
decreasing_by
  · simp_all only [List.length_cons]; omega
  · simp_all only [List.length_cons]; omega

/-- **Given**: `cmin a b ≤ a`. Played (re-derived) in the "Infinity
Arithmetic" level; supplied here so `minCoins_le_of_rep` can cite it. -/
theorem cmin_le_left (a b : ℕ∞) : cmin a b ≤ a := by
  unfold cmin;
  split_ifs <;> simp_all +decide only [le_refl, not_le, le_of_lt]

/-- **Given**: the binary minimum is one of its two arguments. Played
(re-derived) in the "Infinity Arithmetic" level; supplied here so
`minCoins_achievable` can cite it. -/
theorem cmin_eq_left_or_right (a b : ℕ∞) : cmin a b = a ∨ cmin a b = b := by
  unfold cmin; split_ifs <;> simp_all +decide only [true_or, not_le, or_true] ;

/-- `⊤` is the identity for `cmin` on the right. -/
theorem cmin_top (a : ℕ∞) : cmin a ⊤ = a := by
  rw [cmin, if_pos le_top]

/-- **Given**: with positive denominations, no representation uses fewer
coins than the DP value. Out of scope for "Coin Recurrence" (which plays
only the base case `minCoins_zero`); given whole for "Coin Optimality" to
assemble. -/
theorem minCoins_le_of_rep (coins : List ℕ) (amount : ℕ) (hpos : PosCoins coins)
    (r : List ℕ) (hr : IsRep coins amount r) :
    minCoins coins amount ≤ (r.length : ℕ∞) := by
  induction' n : coins.length + amount using Nat.strong_induction_on with n ih generalizing coins amount r; rcases coins with ( _ | ⟨ c, cs ⟩ ) <;> simp_all +decide only [List.length_nil, zero_add, List.length_cons] ;
  · cases r <;> simp_all +decide only [IsRep, and_imp, List.sum_nil, true_and, List.length_nil, List.mem_cons, List.not_mem_nil, imp_false, not_or, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one];
    · rw [← hr]; simp only [minCoins, Nat.cast_zero, le_refl]
    · exact False.elim <| hr.1 _ |>.1 rfl;
  · by_cases hc : c ∈ r <;> simp_all +decide only [IsRep, and_imp, List.mem_cons];
    · have h_erase : minCoins (c :: cs) (amount - c) ≤ (r.erase c).length := by
        apply ih (cs.length + 1 + (amount - c)) (by
        have h_erase : c ≤ amount := by
          exact hr.2 ▸ List.le_sum_of_mem hc;
        linarith [ Nat.sub_add_cancel h_erase, show c > 0 from hpos c ( by simp +decide only [List.mem_cons, true_or] ) ]) (c :: cs) (amount - c) hpos (r.erase c) (by
        intro x hx; exact List.mem_cons.mpr (hr.1 x (List.mem_of_mem_erase hx))) (by
        have hs := hr.2; have he := List.sum_erase hc; omega) (by
        simp +arith +decide only [List.length_cons]);
      have h_erase : minCoins (c :: cs) amount ≤ minCoins (c :: cs) (amount - c) + 1 := by
        rw [ minCoins ];
        simp +decide only [cmin];
        split_ifs <;> simp_all +decide only [List.length_erase_of_mem, ENat.coe_sub, Nat.cast_one, not_le, le_refl, not_and, le_top, not_true_eq_false];
        exact absurd ( ‹0 < c → amount < c› ( hpos c ( by simp +decide only [List.mem_cons, true_or] ) ) ) ( by linarith [ List.le_sum_of_mem hc ] );
      refine le_trans h_erase ?_;
      convert add_le_add_right ‹minCoins ( c :: cs ) ( amount - c ) ≤ ↑ ( r.erase c ).length› 1 using 1;
      · exact add_comm _ _;
      · norm_cast ; rw [ List.length_erase_of_mem hc ] ; simp +arith +decide only;
        rw [ Nat.sub_add_cancel ( List.length_pos_iff.mpr ( List.ne_nil_of_mem hc ) ) ];
    · have h_rep_cs : IsRep cs amount r := by
        exact ⟨ fun x hx => Or.resolve_left ( hr.1 x hx ) fun hx' => hc <| hx'.symm ▸ hx, hr.2 ⟩;
      have h_ind_cs : minCoins cs amount ≤ r.length := by
        exact ih _ ( by linarith ) _ _ ( fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) ) _ h_rep_cs.1 h_rep_cs.2 rfl;
      unfold minCoins; simp +decide only [ge_iff_le] ;
      exact le_trans ( cmin_le_left _ _ ) h_ind_cs

/-- **Given**: if the DP value is finite, some representation uses exactly
that many coins. -/
theorem minCoins_achievable (coins : List ℕ) (amount : ℕ) (n : ℕ)
    (h : minCoins coins amount = (n : ℕ∞)) :
    ∃ r, IsRep coins amount r ∧ r.length = n := by
  revert h n;
  induction' coins with c cs ih generalizing amount;
  · induction' amount with amount ih;
    · simp only [minCoins, IsRep, List.not_mem_nil, imp_false];
      intro n hn; exact ⟨[], ⟨fun _ => List.not_mem_nil, rfl⟩, by exact_mod_cast hn⟩
    · intro n hn
      simp only [minCoins] at hn
      exact absurd hn.symm (ENat.coe_ne_top n)
  · induction' amount using Nat.strong_induction_on with amount ih' generalizing c cs;
    unfold minCoins;
    intro n hn;
    split_ifs at hn;
    · cases cmin_eq_left_or_right ( minCoins cs amount ) ( minCoins ( c :: cs ) ( amount - c ) + 1 ) <;> simp_all +decide only [cmin, ite_eq_left_iff, not_le, ite_eq_right_iff];
      · obtain ⟨ r, hr₁, hr₂ ⟩ := ih _ _ ( by tauto );
        exact ⟨ r, ⟨ fun x hx => List.mem_cons_of_mem _ ( hr₁.1 x hx ), hr₁.2 ⟩, hr₂ ⟩;
      · rcases n with ( _ | n ) <;> simp_all +decide only [CharP.cast_eq_zero, List.length_eq_zero_iff, exists_eq_right, Nat.cast_add, Nat.cast_one, ne_eq, add_left_inj_of_ne_top];
        · exact absurd h.symm (by simp);
        · specialize ih' ( amount - c ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) c cs ( fun amount n hn => ih amount n hn ) n (‹(n : ℕ∞) = minCoins (c :: cs) (amount - c)›.symm);
          obtain ⟨ r, hr₁, hr₂ ⟩ := ih'; use c :: r; simp_all +decide only [IsRep, List.mem_cons, forall_eq_or_imp, true_or, implies_true, and_self, List.sum_cons, add_tsub_cancel_of_le, List.length_cons] ;
    · obtain ⟨ r, hr₁, hr₂ ⟩ := ih _ _ ( by rw [cmin_top] at hn; exact hn : minCoins cs amount = n ) ; use r; simp_all +decide only [IsRep, List.mem_cons, not_and, not_le, or_true, implies_true, and_self] ;

/-- **Given**: with positive denominations, the DP value is `⊤` exactly when
there is no way to make change. -/
theorem minCoins_top_iff_no_rep (coins : List ℕ) (amount : ℕ) (hpos : PosCoins coins) :
    minCoins coins amount = ⊤ ↔ ¬ ∃ r, IsRep coins amount r := by
  constructor;
  · intro htop hrep
    obtain ⟨r, hr⟩ := hrep
    have h_le : minCoins coins amount ≤ (r.length : ℕ∞) :=
      minCoins_le_of_rep coins amount hpos r hr
    rw [htop] at h_le; simp only [top_le_iff] at h_le; exact ENat.coe_ne_top _ h_le;
  · intros h_no_rep
    by_contra h_contra
    have h_finite : ∃ n : ℕ, minCoins coins amount = (n : ℕ∞) := by
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_contra; exact ⟨m, hm.symm⟩;
    obtain ⟨ n, hn ⟩ := h_finite
    obtain ⟨r, hr, _⟩ := minCoins_achievable coins amount n hn
    exact h_no_rep ⟨r, hr⟩

/-- **Given**: the DP recurrence solves coin change — the assembled
least-coins contract. Played (re-assembled) in the "Coin Optimality" level;
supplied here so "Certified Change" can transfer it to the proof-carrying
implementation. -/
theorem minCoins_isLeast (coins : List ℕ) (amount : ℕ) (hpos : PosCoins coins)
    (hne : ∃ r, IsRep coins amount r) :
    IsLeast { n : ℕ∞ | ∃ r, IsRep coins amount r ∧ (r.length : ℕ∞) = n }
      (minCoins coins amount) := by
  refine' ⟨_, fun n hn => _⟩
  · have h_finite : minCoins coins amount ≠ ⊤ := by
      exact fun h => (minCoins_top_iff_no_rep coins amount hpos).mp h hne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h_finite
    obtain ⟨r, hr, hrlen⟩ := minCoins_achievable coins amount n hn.symm
    exact ⟨r, hr, by rw [hrlen]; exact hn⟩
  · obtain ⟨r, hr₁, rfl⟩ := hn
    exact minCoins_le_of_rep coins amount hpos r hr₁

/-- Proof-carrying coin change: the value bundled with a proof it equals the
reference `minCoins coins amount`. -/
def minCarry : (coins : List ℕ) → (amount : ℕ) →
    { v : ℕ∞ // minCoins coins amount = v }
  | [], 0 => ⟨0, by rw [minCoins]⟩
  | [], _ + 1 => ⟨⊤, by rw [minCoins]⟩
  | c :: cs, amount =>
      let r1 := minCarry cs amount
      if h : 0 < c ∧ c ≤ amount then
        let r2 := minCarry (c :: cs) (amount - c)
        ⟨cmin r1.val (r2.val + 1), by
          rw [minCoins, if_pos h]
          exact congr_arg₂ cmin r1.property (congr_arg (· + 1) r2.property)⟩
      else
        ⟨cmin r1.val ⊤, by
          rw [minCoins, if_neg h]
          exact congr_arg₂ cmin r1.property rfl⟩
termination_by coins amount => (coins.length, amount)
decreasing_by
  · simp_all only [List.length_cons]; omega
  · simp_all only [List.length_cons]; omega

/-- The top-level proof-carrying algorithm: just the value component. -/
def coinImpl (coins : List ℕ) (amount : ℕ) : ℕ∞ := (minCarry coins amount).1

/-! ## Lab 07 — dynamic programming: longest common subsequence -/

open List

/-- Longest common subsequence of two lists, by the head-comparison DP
recurrence. -/
def lcs [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: xs, b :: ys =>
      if a = b then a :: lcs xs ys
      else
        let p := lcs (a :: xs) ys
        let q := lcs xs (b :: ys)
        if q.length ≤ p.length then p else q
  termination_by x y => x.length + y.length

/-- **Given**: boundary value — an empty first list has no common
subsequence. Needed by `lcs_sublist_left`/`lcs_sublist_right` and
`lcs_length_max`. -/
theorem lcs_nil_left [DecidableEq α] (ys : List α) : lcs [] ys = [] := by rw [lcs]

/-- **Given**: boundary value — an empty second list has no common
subsequence. -/
theorem lcs_nil_right [DecidableEq α] (xs : List α) : lcs xs [] = [] := by
  cases xs with
  | nil => rw [lcs]
  | cons a t => rw [lcs]; exact fun h => absurd h (List.cons_ne_nil a t)

/-- **Given**: `lcs xs ys` is a subsequence of its first argument. Played
(re-derived) in the "LCS Feasibility" level; supplied here so `lcs_spec`
can cite it. -/
theorem lcs_sublist_left [DecidableEq α] (xs ys : List α) : lcs xs ys <+ xs := by
  induction xs, ys using lcs.induct with
  | case1 x => rw [lcs_nil_left]
  | case2 x hx => rw [lcs_nil_right]; exact List.nil_sublist x
  | case3 xs b ys ih => rw [lcs, if_pos rfl]; exact ih.cons₂ b
  | case4 a xs b ys hab p q hlen ihp ihq => rw [lcs, if_neg hab, if_pos hlen]; exact ihp
  | case5 a xs b ys hab p q hlen ihp ihq =>
      rw [lcs, if_neg hab, if_neg hlen]; exact ihq.trans (List.sublist_cons_self a xs)

/-- **Given**: `lcs xs ys` is a subsequence of its second argument. Played
(re-derived) in the "LCS Feasibility" level; supplied here so `lcs_spec`
can cite it. -/
theorem lcs_sublist_right [DecidableEq α] (xs ys : List α) : lcs xs ys <+ ys := by
  induction xs, ys using lcs.induct with
  | case1 x => rw [lcs_nil_left]; exact List.nil_sublist x
  | case2 x hx => rw [lcs_nil_right]
  | case3 xs b ys ih => rw [lcs, if_pos rfl]; exact ih.cons₂ b
  | case4 a xs b ys hab p q hlen ihp ihq =>
      rw [lcs, if_neg hab, if_pos hlen]; exact ihp.trans (List.sublist_cons_self b ys)
  | case5 a xs b ys hab p q hlen ihp ihq => rw [lcs, if_neg hab, if_neg hlen]; exact ihq

/-- **Given**: optimality — every common subsequence of `xs` and `ys` is no
longer than `lcs xs ys`. Out of scope for "LCS Feasibility" (which plays
only the two sublist facts); given whole for the "LCS Correctness" level to
assemble. -/
theorem lcs_length_max [DecidableEq α] (xs ys : List α) {zs : List α}
    (hx : zs <+ xs) (hy : zs <+ ys) : zs.length ≤ (lcs xs ys).length := by
  induction' hn : xs.length + ys.length using Nat.strong_induction_on with n ih generalizing xs ys zs
  rcases xs with _ | ⟨a, xs⟩
  · rw [List.sublist_nil.mp hx, lcs_nil_left]
  · rcases ys with _ | ⟨b, ys⟩
    · rw [List.sublist_nil.mp hy, lcs_nil_right]
    · by_cases hab : a = b
      · subst hab
        simp only [List.length_cons] at hn
        rw [lcs, if_pos rfl, List.length_cons]
        rcases List.sublist_cons_iff.mp hx with hx' | ⟨r, rfl, hr⟩ <;>
          rcases List.sublist_cons_iff.mp hy with hy' | ⟨s, hs, hs'⟩
        · exact Nat.le_succ_of_le (ih (xs.length + ys.length) (by omega) xs ys hx' hy' rfl)
        · subst hs
          exact Nat.succ_le_succ (ih (xs.length + ys.length) (by omega) xs ys
            ((List.sublist_cons_self a s).trans hx') hs' rfl)
        · exact Nat.succ_le_succ (ih (xs.length + ys.length) (by omega) xs ys
            hr ((List.sublist_cons_self a r).trans hy') rfl)
        · injection hs with _ hrs; subst hrs
          exact Nat.succ_le_succ (ih (xs.length + ys.length) (by omega) xs ys hr hs' rfl)
      · have hlcs : lcs (a :: xs) (b :: ys) =
            if (lcs xs (b :: ys)).length ≤ (lcs (a :: xs) ys).length
            then lcs (a :: xs) ys else lcs xs (b :: ys) := by
          rw [lcs, if_neg hab]
        rw [hlcs]
        split_ifs with hcond
        · rcases List.sublist_cons_iff.mp hy with hy' | ⟨zs', rfl, hzs'⟩
          · exact ih ((a :: xs).length + ys.length) (by simp only [List.length_cons] at hn ⊢; omega) (a :: xs) ys hx hy' rfl
          · rcases List.sublist_cons_iff.mp hx with hx' | ⟨t, hbt, _⟩
            · exact le_trans
                (ih (xs.length + (b :: ys).length) (by simp only [List.length_cons] at hn ⊢; omega) xs (b :: ys) hx' hy rfl) hcond
            · injection hbt with hba _; exact absurd hba.symm hab
        · rcases List.sublist_cons_iff.mp hy with hy' | ⟨zs', rfl, hzs'⟩
          · exact le_trans
              (ih ((a :: xs).length + ys.length) (by simp only [List.length_cons] at hn ⊢; omega) (a :: xs) ys hx hy' rfl)
              (le_of_lt (not_le.mp hcond))
          · rcases List.sublist_cons_iff.mp hx with hx' | ⟨t, hbt, _⟩
            · exact ih (xs.length + (b :: ys).length) (by simp only [List.length_cons] at hn ⊢; omega) xs (b :: ys) hx' hy rfl
            · injection hbt with hba _; exact absurd hba.symm hab

/-- **Given**: packaged specification — `lcs xs ys` is a common subsequence
of maximum length. Played (re-assembled) in the "LCS Correctness" level; supplied
here so "Certified LCS" can transfer it to the proof-carrying
implementation. -/
theorem lcs_spec [DecidableEq α] (xs ys : List α) :
    (lcs xs ys <+ xs) ∧ (lcs xs ys <+ ys) ∧
      (∀ zs : List α, zs <+ xs → zs <+ ys → zs.length ≤ (lcs xs ys).length) :=
  ⟨lcs_sublist_left xs ys, lcs_sublist_right xs ys, fun _ hx hy => lcs_length_max xs ys hx hy⟩

/-- Proof-carrying LCS: returns the value together with a proof that it
equals the reference value `lcs xs ys`. -/
def lcsCarry [DecidableEq α] : (xs ys : List α) → { v : List α // lcs xs ys = v }
  | [], _ => ⟨[], by unfold lcs; rfl⟩
  | _ :: _, [] => ⟨[], by unfold lcs; rfl⟩
  | a :: xs, b :: ys =>
      if h : a = b then
        let r := lcsCarry xs ys
        ⟨a :: r.val, by unfold lcs; rw [if_pos h]; exact congr_arg (a :: ·) r.property⟩
      else
        let p := lcsCarry (a :: xs) ys
        let q := lcsCarry xs (b :: ys)
        if hpq : q.val.length ≤ p.val.length then
          ⟨p.val, by
            unfold lcs; rw [if_neg h]
            simp only [p.property, q.property]
            rw [if_pos hpq]⟩
        else
          ⟨q.val, by
            unfold lcs; rw [if_neg h]
            simp only [p.property, q.property]
            rw [if_neg hpq]⟩
  termination_by x y => x.length + y.length

/-- The top-level proof-carrying algorithm: just the value component. -/
def lcsImpl [DecidableEq α] (xs ys : List α) : List α := (lcsCarry xs ys).1

/-! ## Lab 08 — dynamic programming: optimal binary search trees -/

/-- The shape of a binary search tree: `leaf` is an empty subtree, `node l r`
has left/right subtrees. -/
inductive Shape where
  /-- An empty subtree. -/
  | leaf : Shape
  /-- A node with a left and a right subtree. -/
  | node : Shape → Shape → Shape
  deriving Repr, DecidableEq

/-- The number of keys (internal nodes) stored in a shape. -/
def numKeys : Shape → ℕ
  | .leaf => 0
  | .node l r => numKeys l + numKeys r + 1

/-- `Wsum w i len = w i + w (i+1) + … + w (i+len-1)`: the total access
weight of the key interval `[i, i+len)`. -/
def Wsum (w : ℕ → ℕ) (i len : ℕ) : ℕ := ∑ k ∈ Finset.range len, w (i + k)

/-- Cost of a shape placed over the interval starting at key `i`, with the
root at depth `d`. -/
def scost (w : ℕ → ℕ) : Shape → ℕ → ℕ → ℕ
  | .leaf, _, _ => 0
  | .node l r, i, d =>
      (d + 1) * w (i + numKeys l) + scost w l i (d + 1) + scost w r (i + numKeys l + 1) (d + 1)

/-- The total cost of a shape over the interval starting at key `i` (root
at depth `0`). -/
def tcost (w : ℕ → ℕ) (s : Shape) (i : ℕ) : ℕ := scost w s i 0

/-- **Given**: splitting the interval weight around a root key. -/
theorem Wsum_split (w : ℕ → ℕ) (i a b : ℕ) :
    Wsum w i (a + 1 + b) = Wsum w i a + w (i + a) + Wsum w (i + a + 1) b := by
  simp +arith +decide [ Wsum, Finset.sum_range_add ];
  exact Nat.recOn b ( by norm_num ) fun n ih => by simp_all +decide [ add_assoc, Finset.sum_range_succ ] ; linarith;

/-- **Given**: placing a shape one level deeper adds its whole interval
weight once per level. -/
theorem scost_depth (w : ℕ → ℕ) (s : Shape) (i d : ℕ) :
    scost w s i d = scost w s i 0 + d * Wsum w i (numKeys s) := by
  induction' s with l r hl hr generalizing i d;
  · simp [scost, numKeys, Wsum];
  · rw [ show numKeys ( l.node r ) = numKeys l + numKeys r + 1 from rfl, show Wsum w i ( numKeys l + numKeys r + 1 ) = Wsum w i ( numKeys l ) + w ( i + numKeys l ) + Wsum w ( i + numKeys l + 1 ) ( numKeys r ) from ?_ ];
    · rw [ show scost w ( l.node r ) i d = ( d + 1 ) * w ( i + numKeys l ) + scost w l i ( d + 1 ) + scost w r ( i + numKeys l + 1 ) ( d + 1 ) from rfl, show scost w ( l.node r ) i 0 = ( 0 + 1 ) * w ( i + numKeys l ) + scost w l i 1 + scost w r ( i + numKeys l + 1 ) 1 from rfl ] ; rw [ hl, hr, hl, hr ] ;
      rw [hl i 1, hr (i + numKeys l + 1) 1]; ring
    · convert Wsum_split w i ( numKeys l ) ( numKeys r ) using 1;
      grobner

/-- **Given**: the cost recurrence that justifies the DP — a root
contributes the whole interval weight on top of the two subtree costs. -/
theorem tcost_node (w : ℕ → ℕ) (l r : Shape) (i : ℕ) :
    tcost w (.node l r) i =
      tcost w l i + tcost w r (i + numKeys l + 1) + Wsum w i (numKeys (.node l r)) := by
  unfold tcost
  rw [show scost w (.node l r) i 0
        = (0 + 1) * w (i + numKeys l) + scost w l i 1 + scost w r (i + numKeys l + 1) 1 from rfl,
    scost_depth w l i 1, scost_depth w r (i + numKeys l + 1) 1,
    show numKeys (.node l r) = numKeys l + 1 + numKeys r from by
      show numKeys l + numKeys r + 1 = numKeys l + 1 + numKeys r; omega,
    Wsum_split w i (numKeys l) (numKeys r)]
  ring

/-- `minRoots f n = min (f 0) (f 1) … (f n)`: the best over all `n+1`
candidate roots. -/
def minRoots (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => min (f (n + 1)) (minRoots f n)

/-- **Given**: `minRoots` only depends on the values of `f` on `0 … n`. -/
theorem minRoots_congr {f g : ℕ → ℕ} (n : ℕ) (h : ∀ r ≤ n, f r = g r) :
    minRoots f n = minRoots g n := by
  induction' n with n ih;
  · exact h 0 bot_le;
  · rw [ show minRoots f ( n + 1 ) = min ( f ( n + 1 ) ) ( minRoots f n ) from rfl, show minRoots g ( n + 1 ) = min ( g ( n + 1 ) ) ( minRoots g n ) from rfl, h _ ( Nat.le_refl _ ), ih fun r hr => h _ ( Nat.le_succ_of_le hr ) ]

/-- **Given**: `minRoots f n` is `≤ f r` for every candidate `r ≤ n`.
Played (re-derived) in the "Root Candidates" level; supplied here so
`exists_tcost_eq_optCost`/`optCost_le_tcost` can cite it. -/
theorem minRoots_le (f : ℕ → ℕ) (n : ℕ) : ∀ r ≤ n, minRoots f n ≤ f r := by
  induction' n with n ih;
  · intro r hr; rw [Nat.le_zero.mp hr]; simp only [minRoots, le_refl]
  · intro r hr; cases hr <;> simp_all +decide [ minRoots ] ;

/-- **Given**: `minRoots f n` is attained at some candidate `r ≤ n`. Played
(re-derived) in the "Root Candidates" level; supplied here so
`exists_tcost_eq_optCost` can cite it. -/
theorem minRoots_exists (f : ℕ → ℕ) (n : ℕ) : ∃ r ≤ n, minRoots f n = f r := by
  induction' n with n ih;
  · exact ⟨ 0, by norm_num, rfl ⟩;
  · obtain ⟨r0, hr0, hr0eq⟩ := ih
    rw [minRoots]
    rcases le_total (f (n + 1)) (minRoots f n) with hle | hle
    · exact ⟨n + 1, Nat.le_refl _, min_eq_left hle⟩
    · exact ⟨r0, Nat.le_succ_of_le hr0, by rw [min_eq_right hle]; exact hr0eq⟩

/-- The interval DP, with an explicit `fuel` counter so termination is
structural. -/
def obst (w : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | _ + 1, _, 0 => 0
  | fuel + 1, i, len + 1 =>
      Wsum w i (len + 1) +
        minRoots (fun r => obst w fuel i r + obst w fuel (i + r + 1) (len - r)) len

/-- **Given**: fuel independence — any fuel `≥ len` gives the same value. -/
theorem obst_fuel (w : ℕ → ℕ) : ∀ (len fuel i : ℕ), len ≤ fuel →
    obst w fuel i len = obst w len i len := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro fuel i h
    rcases len with _ | m
    · cases fuel <;> rfl
    · obtain ⟨fuel', rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_succ_le h)
      simp only [obst]
      congr 1
      apply minRoots_congr
      intro r hr
      rw [ih r (by omega) (m + fuel') i (by omega), ih r (by omega) m i (by omega),
        ih (m - r) (by omega) (m + fuel') (i + r + 1) (by omega),
        ih (m - r) (by omega) m (i + r + 1) (by omega)]

/-- The optimal-BST DP value for the key interval `[i, i+len)`. -/
def optCost (w : ℕ → ℕ) (i len : ℕ) : ℕ := obst w len i len

/-- **Given**: base case of the recurrence. -/
theorem optCost_zero (w : ℕ → ℕ) (i : ℕ) : optCost w i 0 = 0 := rfl

/-- **Given**: the optimal-BST recurrence. -/
theorem optCost_succ (w : ℕ → ℕ) (i len : ℕ) :
    optCost w i (len + 1) =
      Wsum w i (len + 1) +
        minRoots (fun r => optCost w i r + optCost w (i + r + 1) (len - r)) len := by
  have h_minRoots_congr : minRoots (fun r => obst w len i r + obst w len (i + r + 1) (len - r)) len = minRoots (fun r => optCost w i r + optCost w (i + r + 1) (len - r)) len := by
    apply minRoots_congr;
    exact fun r hr => congr_arg₂ ( · + · ) ( obst_fuel w _ _ _ ( by omega ) ) ( obst_fuel w _ _ _ ( by omega ) );
  convert congr_arg _ h_minRoots_congr using 1

/-- **Given**: lower bound — no tree shape on `len` keys costs less than
the DP value. Out of scope for "Root Candidates" (which plays only
`minRoots_le`/`minRoots_exists`); given whole for "Optimal Tree" to
assemble. -/
theorem optCost_le_tcost (w : ℕ → ℕ) : ∀ (len i : ℕ) (s : Shape), numKeys s = len →
    optCost w i len ≤ tcost w s i := by
  intro len i s;
  induction' len using Nat.strong_induction_on with len ih generalizing i s;
  rcases s with ( _ | ⟨ l, r ⟩ ) <;> intro h;
  · subst h; exact optCost_zero _ _ ▸ by rfl;
  · rw [ show len = numKeys l + numKeys r + 1 from h.symm ];
    rw [ tcost_node, optCost_succ ];
    rw [ add_comm ];
    refine' add_le_add _ _;
    · refine' le_trans ( minRoots_le _ _ _ _ ) _;
      exact numKeys l;
      · exact Nat.le_add_right _ _;
      · simp +zetaDelta at *;
        exact add_le_add ( ih _ ( by linarith! [ show numKeys l + numKeys r + 1 = len from h ] ) _ _ rfl ) ( ih _ ( by linarith! [ show numKeys l + numKeys r + 1 = len from h ] ) _ _ rfl );
    · rfl

/-- **Given**: achievability — some tree shape on `len` keys attains the DP
value. Given whole for "Optimal Tree" to assemble. -/
theorem exists_tcost_eq_optCost (w : ℕ → ℕ) : ∀ (len i : ℕ),
    ∃ s : Shape, numKeys s = len ∧ tcost w s i = optCost w i len := by
  intro len;
  induction' len using Nat.strong_induction_on with len ih generalizing w;
  rcases len with ( _ | len ) <;> simp_all +decide [ optCost_succ ];
  · exact fun i => ⟨ .leaf, rfl, rfl ⟩;
  · intro i
    obtain ⟨r0, hr0⟩ : ∃ r0 ≤ len, minRoots (fun r => optCost w i r + optCost w (i + r + 1) (len - r)) len = optCost w i r0 + optCost w (i + r0 + 1) (len - r0) := by
      exact minRoots_exists (fun r => optCost w i r + optCost w (i + r + 1) (len - r)) len
    obtain ⟨sl, hsl⟩ := ih r0 hr0.left w i
    obtain ⟨sr, hsr⟩ := ih (len - r0) (Nat.sub_le len r0) w (i + r0 + 1);
    use .node sl sr;
    simp_all +decide [ numKeys, tcost_node ];
    ring

/-- **Given**: optimality of the DP — the assembled least-cost contract.
Played (re-assembled) in the "Optimal Tree" boss level; supplied here so
"Certified Tree" can transfer it to the proof-carrying implementation. -/
theorem optCost_isLeast (w : ℕ → ℕ) (i len : ℕ) :
    IsLeast {c | ∃ s : Shape, numKeys s = len ∧ tcost w s i = c} (optCost w i len) := by
  constructor
  · obtain ⟨s, hs, hc⟩ := exists_tcost_eq_optCost w len i
    exact ⟨s, hs, hc⟩
  · rintro c ⟨s, hs, rfl⟩
    exact optCost_le_tcost w len i s hs

/-- Proof-carrying minimum over candidate roots. -/
def minRootsCarry {f : ℕ → ℕ} (g : (r : ℕ) → { v : ℕ // f r = v }) :
    (n : ℕ) → { v : ℕ // minRoots f n = v }
  | 0 => ⟨(g 0).val, by unfold minRoots; exact (g 0).property⟩
  | n + 1 =>
      let hd := g (n + 1)
      let tl := minRootsCarry g n
      ⟨min hd.val tl.val, by
        unfold minRoots; exact congr_arg₂ min hd.property tl.property⟩

/-- Proof-carrying fuelled interval DP. -/
def obstCarry (w : ℕ → ℕ) : (fuel i len : ℕ) → { v : ℕ // obst w fuel i len = v }
  | 0, _, _ => ⟨0, by unfold obst; rfl⟩
  | _ + 1, _, 0 => ⟨0, by unfold obst; rfl⟩
  | fuel + 1, i, len + 1 =>
      let f : ℕ → ℕ := fun r => obst w fuel i r + obst w fuel (i + r + 1) (len - r)
      let g : (r : ℕ) → { v : ℕ // f r = v } := fun r =>
        ⟨(obstCarry w fuel i r).val + (obstCarry w fuel (i + r + 1) (len - r)).val,
          congr_arg₂ (· + ·) (obstCarry w fuel i r).property
            (obstCarry w fuel (i + r + 1) (len - r)).property⟩
      let m := minRootsCarry (f := f) g len
      ⟨Wsum w i (len + 1) + m.val, by
        unfold obst; exact congr_arg (Wsum w i (len + 1) + ·) m.property⟩
  termination_by fuel _ _ => fuel
  decreasing_by all_goals omega

/-- Proof-carrying optimal-BST DP value for the interval `[i, i+len)`. -/
def optCarry (w : ℕ → ℕ) (i len : ℕ) : { v : ℕ // optCost w i len = v } :=
  let r := obstCarry w len i len
  ⟨r.val, by unfold optCost; exact r.property⟩

/-- The top-level proof-carrying algorithm: just the value component. -/
def optImpl (w : ℕ → ℕ) (i len : ℕ) : ℕ := (optCarry w i len).1

/-! ## Lab 09 — dynamic programming: maximum subarray (Kadane's algorithm) -/

/-- The largest sum of a prefix of `l` (a contiguous block starting at
index `0`), clamped at `0` for the empty prefix. -/
def maxPrefixSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => max 0 (x + maxPrefixSum xs)

/-- The largest sum of any contiguous block of `l`, allowing the empty
block. -/
def maxSubSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => max (maxPrefixSum (x :: xs)) (maxSubSum xs)

/-- One left-to-right pass maintaining the accumulator `(p, b)` = (best
prefix sum, best block sum). -/
def kadaneAux : List ℤ → ℤ × ℤ
  | [] => (0, 0)
  | x :: xs =>
      let b0 := kadaneAux xs
      let p := max 0 (x + b0.1)
      (p, max p b0.2)

/-- Kadane's algorithm: the maximum subarray sum, read off the
accumulator. -/
def kadane (l : List ℤ) : ℤ := (kadaneAux l).2

/-- The set of all contiguous-block sums of `l` (including the empty
block, sum `0`). -/
def subSums (l : List ℤ) : Set ℤ := { s | ∃ i j : ℕ, s = ((l.take j).drop i).sum }

/-- **Given**: `maxPrefixSum` is nonnegative. -/
theorem maxPrefixSum_nonneg (l : List ℤ) : 0 ≤ maxPrefixSum l := by
  induction' l with x xs ih;
  · rfl;
  · exact le_max_left _ _

/-- **Given**: `maxSubSum` is nonnegative. Needed by `maxSubSum_ub`. -/
theorem maxSubSum_nonneg (l : List ℤ) : 0 ≤ maxSubSum l := by
  induction' l with x l ih <;> simp_all +decide [ maxSubSum ]

/-- **Given**: `maxPrefixSum l` upper-bounds the sum of every prefix
`l.take j`. Played (re-derived) in the "Max Prefix Sum Upper Bound" level; supplied
here so `maxSubSum_ub` can cite it. -/
theorem maxPrefixSum_ub (l : List ℤ) (j : ℕ) : (l.take j).sum ≤ maxPrefixSum l := by
  induction' l with x l ih generalizing j;
  · cases j <;> trivial;
  · rcases j with ( _ | j ) <;> simp_all +decide [ maxPrefixSum ]

/-- **Given**: `maxPrefixSum l` is attained by some prefix `l.take j`.
Needed by `maxSubSum_mem`. -/
theorem maxPrefixSum_mem (l : List ℤ) : ∃ j : ℕ, (l.take j).sum = maxPrefixSum l := by
  induction' l with x l ih;
  · exists 0;
  · cases le_total 0 ( x + maxPrefixSum l ) <;> simp_all +decide [ maxPrefixSum ];
    · obtain ⟨ j, hj ⟩ := ih; use j + 1; simp +decide [ hj ] ;
    · exact ⟨ 0, rfl ⟩

/-- **Given**: `maxSubSum l` upper-bounds the sum of every contiguous block
`(l.take j).drop i`. Needed by `kadane_isGreatest`. -/
theorem maxSubSum_ub (l : List ℤ) (i j : ℕ) : ((l.take j).drop i).sum ≤ maxSubSum l := by
  induction' l with x l ih generalizing i j;
  · aesop;
  · rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide [ List.take, List.drop ];
    · exact maxSubSum_nonneg _;
    · refine' le_trans _ ( le_max_left _ _ );
      exact le_max_of_le_right ( by simpa using maxPrefixSum_ub l j );
    · exact maxSubSum_nonneg (x :: l);
    · exact le_trans ( ih i j ) ( le_max_right _ _ )

/-- **Given**: `maxSubSum l` is attained by some contiguous block
`(l.take j).drop i`. Out of scope for "Max Prefix Sum Upper Bound" (bonus there);
given whole since `kadane_isGreatest` needs it. -/
theorem maxSubSum_mem (l : List ℤ) : ∃ i j : ℕ, ((l.take j).drop i).sum = maxSubSum l := by
  induction' l with x xs ih;
  · exists 0, 0;
  · have h_max : maxSubSum (x :: xs) = max (maxPrefixSum (x :: xs)) (maxSubSum xs) := by
      rfl;
    cases max_cases ( maxPrefixSum ( x :: xs ) ) ( maxSubSum xs ) <;> simp_all +decide;
    · obtain ⟨ j, hj ⟩ := maxPrefixSum_mem ( x :: xs );
      exact ⟨ 0, j, by simpa using hj ⟩;
    · obtain ⟨ i, j, h ⟩ := ih; use i + 1, j + 1; aesop;

/-- **Given**: the loop invariant — Kadane's accumulator computes the
reference quantities. Played (re-derived) in the "Kadane Invariant" level;
supplied here so `kadane_isGreatest` can cite `kadane_eq`. -/
theorem kadaneAux_eq (l : List ℤ) : kadaneAux l = (maxPrefixSum l, maxSubSum l) := by
  induction' l with x xs ih;
  · rfl;
  · simp [maxSubSum, maxPrefixSum];
    rw [ show kadaneAux ( x :: xs ) = ( max 0 ( x + ( kadaneAux xs ).1 ), max ( max 0 ( x + ( kadaneAux xs ).1 ) ) ( kadaneAux xs ).2 ) from rfl, ih ] ; aesop

/-- **Given**: reading off the invariant — `kadane` computes `maxSubSum`. -/
theorem kadane_eq (l : List ℤ) : kadane l = maxSubSum l := by
  exact congr_arg Prod.snd ( kadaneAux_eq l )

/-! ## Lab 10 — string matching: naive and Rabin–Karp -/

/-- The pattern `pat` occurs in `text` starting at index `i`. -/
def matchAt (text pat : List ℕ) (i : ℕ) : Prop := (text.drop i).take pat.length = pat

instance (text pat : List ℕ) (i : ℕ) : Decidable (matchAt text pat i) := by
  unfold matchAt; infer_instance

/-- The naive matcher: return every candidate position `i ≤ |text|` at
which the pattern matches, by direct comparison. -/
def naiveMatches (text pat : List ℕ) : List ℕ :=
  (List.range (text.length + 1)).filter (fun i => decide ((text.drop i).take pat.length = pat))

/-- The polynomial (Horner) hash of a list of character codes in base
`B`. -/
def hashList (B : ℕ) (l : List ℕ) : ℕ := l.foldl (fun h c => h * B + c) 0

/-- **Given**: two blocks that are equal have equal hashes — the direction
Rabin–Karp relies on. Needed by `rkMatches_eq_naiveMatches`. -/
theorem hashList_eq_of_eq (B : ℕ) {l₁ l₂ : List ℕ} (h : l₁ = l₂) :
    hashList B l₁ = hashList B l₂ := by
  rw [h]

/-- The Rabin–Karp matcher in base `B`: accept a position when the
window's fingerprint equals the pattern's fingerprint and the window
really equals the pattern. -/
def rkMatches (B : ℕ) (text pat : List ℕ) : List ℕ :=
  (List.range (text.length + 1)).filter (fun i =>
    decide (hashList B ((text.drop i).take pat.length) = hashList B pat) &&
    decide ((text.drop i).take pat.length = pat))

/-- **Given**: specification of the naive matcher — it returns exactly the
matching positions `i ≤ |text|`. Played (re-derived) in the "Naive
Matching" level; supplied here so `mem_rkMatches` can cite it. -/
theorem mem_naiveMatches (text pat : List ℕ) (i : ℕ) :
    i ∈ naiveMatches text pat ↔ i ≤ text.length ∧ matchAt text pat i := by
  unfold naiveMatches matchAt
  rw [List.mem_filter, List.mem_range, Nat.lt_add_one_iff, decide_eq_true_eq]

end Game.Design
