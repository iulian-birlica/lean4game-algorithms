import Mathlib
import Game.Support.TimeM

/-! Answer-free definitions and given (already-proven) facts used by the
Complexity and Computability worlds. Most of this support is ported from
`RequestProject/Lab19Reductions.lean`, `Lab20ComplexityClasses.lean`,
`Lab21Decidability.lean`, and `Lab22HaltingAndBusyBeaver.lean`, with
additional lightweight definitions mirrored from the older game tree. As elsewhere,
theorems here are either prerequisites a level's proof is allowed to
cite, or genuinely out-of-scope infrastructure — the level files still
perform the calculus/assembly proof the lab teaches. No level solutions
live here. -/
namespace Game.Complexity

open Cslib.Algorithms.Lean
open Classical

/-! ## Lab 19, Part 1 — polynomially bounded functions -/

/-- A cost/growth function `t : ℕ → ℕ` is **polynomially bounded** if it
is dominated by a single monomial `c·(n+1)^k`. -/
def IsPolyBounded (t : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, t n ≤ c * (n + 1) ^ k

/-- **Given**: a constant function is polynomially bounded. Needed by
`PolyReducible.refl`. -/
theorem IsPolyBounded.const (c : ℕ) : IsPolyBounded (fun _ => c) := by
  exact ⟨ c, 0, fun n => by norm_num ⟩

/-- **Given**: the monomial `n ↦ c·(n+1)^k` is polynomially bounded (by
itself). Needed by the reduction-assembly levels. -/
theorem IsPolyBounded.monomial (c k : ℕ) : IsPolyBounded (fun n => c * (n + 1) ^ k) := by
  exact ⟨ c, k, fun n => le_rfl ⟩

/-- **Given**: the affine function `n ↦ c·(n+1)` is polynomially bounded.
Needed by the reduction-assembly levels. -/
theorem IsPolyBounded.linear (c : ℕ) : IsPolyBounded (fun n => c * (n + 1)) :=
  ⟨c, 1, fun n => by rw [pow_one]⟩

/-- **Given**: the identity is polynomially bounded. Needed by
`PolyReducible.refl`. -/
theorem IsPolyBounded.id : IsPolyBounded (fun n => n) := by
  exact ⟨ 1, 1, fun n => by nlinarith ⟩

/-- **Given**: a function bounded pointwise by a polynomially bounded
function is polynomially bounded. Not needed elsewhere, but recorded for
completeness. -/
theorem IsPolyBounded.of_le {t u : ℕ → ℕ} (hu : IsPolyBounded u) (h : ∀ n, t n ≤ u n) :
    IsPolyBounded t := by
  rcases hu with ⟨ c, k, hu ⟩ ; exact ⟨ c, k, fun n ↦ le_trans ( h n ) ( hu n ) ⟩ ;

/-- **Given**: two monomial bounds combine into one — the key arithmetic
step behind closure under addition. Played (re-derived) in the
"Polynomial Time Reductions" level; supplied here so `PolyTimeSolvable.of_reducible`
and the reduction-composition proofs can cite it. -/
theorem monomial_add_bound {a b n c₁ k₁ c₂ k₂ : ℕ}
    (ha : a ≤ c₁ * (n + 1) ^ k₁) (hb : b ≤ c₂ * (n + 1) ^ k₂) :
    a + b ≤ (c₁ + c₂) * (n + 1) ^ max k₁ k₂ := by
  rw [ add_mul ];
  exact add_le_add ( ha.trans ( Nat.mul_le_mul_left _ ( pow_le_pow_right₀ ( Nat.succ_pos _ ) ( Nat.le_max_left _ _ ) ) ) ) ( hb.trans ( Nat.mul_le_mul_left _ ( pow_le_pow_right₀ ( Nat.succ_pos _ ) ( Nat.le_max_right _ _ ) ) ) )

/-- **Given**: feeding a polynomial bound into a monomial stays
polynomial — the key arithmetic step behind closure under composition.
Played (re-derived) in the "Polynomial Time Reductions" level; supplied here so
`PolyTimeSolvable.of_reducible` and `PolyReducible.trans` can cite it. -/
theorem monomial_comp_bound {y n cs ks c₂ k₂ : ℕ} (hy : y ≤ cs * (n + 1) ^ ks) :
    c₂ * (y + 1) ^ k₂ ≤ (c₂ * (cs + 1) ^ k₂) * (n + 1) ^ (ks * k₂) := by
  rw [ Nat.pow_mul ];
  rw [ mul_assoc ];
  rw [ ← mul_pow ] ; gcongr ; nlinarith [ pow_pos ( by linarith : 0 < n + 1 ) ks ]

/-- **Given**: polynomially bounded functions are closed under
(pointwise) addition. Played (re-derived) in the "Polynomial Time Reductions"
level; supplied here so `PolyTimeSolvable.of_reducible` can cite it. -/
theorem IsPolyBounded.add {t u : ℕ → ℕ} (ht : IsPolyBounded t) (hu : IsPolyBounded u) :
    IsPolyBounded (fun n => t n + u n) := by
  exact ⟨ ht.choose + hu.choose, max ht.choose_spec.choose hu.choose_spec.choose, fun n => monomial_add_bound ( ht.choose_spec.choose_spec n ) ( hu.choose_spec.choose_spec n ) ⟩

/-- **Given**: polynomially bounded functions are closed under
composition. Played (re-derived) in the "Polynomial Time Reductions" level;
supplied here so `PolyTimeSolvable.of_reducible` can cite it. -/
theorem IsPolyBounded.comp {t u : ℕ → ℕ} (ht : IsPolyBounded t) (hu : IsPolyBounded u) :
    IsPolyBounded (fun n => t (u n)) := by
  obtain ⟨ c, k, hc ⟩ := ht;
  obtain ⟨ cs, ks, hcs ⟩ := hu;
  exact ⟨ c * ( cs + 1 ) ^ k, ks * k, fun n => by simpa only [ mul_assoc ] using le_trans ( hc _ ) ( monomial_comp_bound ( hcs _ ) ) ⟩

/-! ## Lab 19, Part 2 — polynomial-time solvability and reductions -/

/-- `P` (with size measure `size`) is **polynomial-time solvable** if
there is a solver `alg : α → TimeM ℕ Bool` that returns `true` exactly on
the yes-instances and whose running time is polynomially bounded in the
input size. -/
def PolyTimeSolvable {α : Type*} (size : α → ℕ) (P : α → Prop) : Prop :=
  ∃ (alg : α → TimeM ℕ Bool) (t : ℕ → ℕ),
    IsPolyBounded t ∧
    (∀ x, ((alg x).ret = true ↔ P x)) ∧
    (∀ x, (alg x).time ≤ t (size x))

/-- A **polynomial-time (many–one) reduction** from `(A, sizeA)` to
`(B, sizeB)`. -/
def PolyReducible {α β : Type*} (sizeA : α → ℕ) (sizeB : β → ℕ)
    (A : α → Prop) (B : β → Prop) : Prop :=
  ∃ (f : α → β) (red : α → TimeM ℕ β) (t s : ℕ → ℕ),
    IsPolyBounded t ∧ IsPolyBounded s ∧
    (∀ x, (red x).ret = f x) ∧
    (∀ x, (A x ↔ B (f x))) ∧
    (∀ x, (red x).time ≤ t (sizeA x)) ∧
    (∀ x, sizeB (f x) ≤ s (sizeA x))

/-- **Given**: a convenient way to build a reduction from a plain
instance map `f`, isolating the two mathematical obligations of a Karp
reduction (answer preservation and polynomial size blow-up). Needed by
every reduction-assembly level. -/
theorem PolyReducible.of_map {α β : Type*} {sizeA : α → ℕ} {sizeB : β → ℕ}
    {A : α → Prop} {B : β → Prop}
    (f : α → β) (s : ℕ → ℕ) (hs : IsPolyBounded s)
    (hcorr : ∀ x, (A x ↔ B (f x)))
    (hsize : ∀ x, sizeB (f x) ≤ s (sizeA x)) :
    PolyReducible sizeA sizeB A B := by
  refine ⟨f, fun x => ⟨f x, sizeB (f x)⟩, s, s, hs, hs, fun _ => rfl, hcorr, hsize, hsize⟩

/-! ## Lab 19, Part 3 — the calculus of reductions -/

/-- **Given**: composition principle — if `A` reduces to `B` in
polynomial time and `B` is polynomial-time solvable, then `A` is
polynomial-time solvable. Needed by `inP_of_reduces`. -/
theorem PolyTimeSolvable.of_reducible {α β : Type*} {sizeA : α → ℕ} {sizeB : β → ℕ}
    {A : α → Prop} {B : β → Prop}
    (hred : PolyReducible sizeA sizeB A B) (hB : PolyTimeSolvable sizeB B) :
    PolyTimeSolvable sizeA A := by
  revert hred hB;
  unfold PolyReducible PolyTimeSolvable;
  simp +zetaDelta only [exists_and_left, forall_exists_index, and_imp] at *;
  intro f red t ht s hs hret hcorr htime hsize alg tB htB halgret halgtime; use fun x => TimeM.bind (red x) alg; simp_all +decide only [TimeM.bind, implies_true, true_and] ;
  obtain ⟨c, k, hc⟩ := htB;
  use fun n => t n + c * (s n + 1) ^ k; (
  refine' ⟨ _, _ ⟩;
  · apply IsPolyBounded.add ht (IsPolyBounded.comp (IsPolyBounded.monomial c k) hs);
  · exact fun x => add_le_add ( htime x ) ( le_trans ( halgtime _ ) ( hc _ |> le_trans <| Nat.mul_le_mul_left _ <| Nat.pow_le_pow_left ( Nat.succ_le_succ <| hsize _ ) _ ) ))

/-- **Given**: reducibility is reflexive — every problem reduces to
itself via the identity, computed for free. Played (re-derived) in the
"Reduction Calculus" level; supplied here in case a later section needs
it. -/
theorem PolyReducible.refl {α : Type*} (size : α → ℕ) (A : α → Prop) :
    PolyReducible size size A A := by
  use fun x => x, fun x => pure x;
  refine' ⟨ fun _ => 0, fun n => n, _, _, _, _, _ ⟩ <;> simp +decide only [IsPolyBounded.const, IsPolyBounded.id, TimeM.ret_pure, implies_true, TimeM.time_pure, le_refl, and_self]

/-- **Given**: reducibility is transitive. Played (re-derived) in the
"Reduction Calculus" level; supplied here in case a later section needs
it. -/
theorem PolyReducible.trans {α β γ : Type*} {sizeA : α → ℕ} {sizeB : β → ℕ} {sizeC : γ → ℕ}
    {A : α → Prop} {B : β → Prop} {C : γ → Prop}
    (hAB : PolyReducible sizeA sizeB A B) (hBC : PolyReducible sizeB sizeC B C) :
    PolyReducible sizeA sizeC A C := by
  rcases hAB with ⟨ f₁, red₁, t₁, s₁, ht₁, hs₁, hf₁, hAB₁, ht₁', hs₁' ⟩;
  rcases hBC with ⟨ f₂, red₂, t₂, s₂, h_interm ⟩;
  obtain ⟨ c₁, k₁, ht₁ ⟩ := ht₁
  obtain ⟨ c₂, k₂, ht₂ ⟩ := h_interm.left
  obtain ⟨ c₃, k₃, hs₁ ⟩ := hs₁
  obtain ⟨ c₄, k₄, hs₂ ⟩ := h_interm.right.left
  use f₂ ∘ f₁;
  refine' ⟨ fun x => TimeM.mk ( f₂ ( f₁ x ) ) ( ( red₁ x |> TimeM.time ) + ( red₂ ( f₁ x ) |> TimeM.time ) ), fun n => ( c₁ * ( n + 1 ) ^ k₁ ) + ( c₂ * ( c₃ * ( n + 1 ) ^ k₃ + 1 ) ^ k₂ ), fun n => c₄ * ( c₃ * ( n + 1 ) ^ k₃ + 1 ) ^ k₄, _, _, _, _, _ ⟩;
  · exact ⟨ c₁ + c₂ * ( c₃ + 1 ) ^ k₂, k₁ ⊔ ( k₃ * k₂ ), fun n => monomial_add_bound ( by simp only [le_refl] ) ( by simpa only using monomial_comp_bound (by simp only [le_refl]) ) ⟩;
  · exact ⟨ c₄ * ( c₃ + 1 ) ^ k₄, k₃ * k₄, fun n => by simpa only [pow_mul, mul_assoc] using monomial_comp_bound (show c₃ * (n + 1) ^ k₃ ≤ c₃ * (n + 1) ^ k₃ from le_rfl) ⟩;
  · grobner;
  · intro x; exact (hAB₁ x).trans (h_interm.2.2.2.1 (f₁ x))
  · refine' ⟨ fun x => _, fun x => _ ⟩;
    · refine' add_le_add ( le_trans ( ht₁' x ) ( ht₁ _ ) ) ( le_trans ( h_interm.2.2.2.2.1 _ ) ( le_trans ( ht₂ _ ) _ ) );
      exact Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left ( by linarith [ hs₁' x, hs₁ ( sizeA x ) ] ) _ );
    · exact le_trans ( h_interm.2.2.2.2.2 _ ) ( le_trans ( hs₂ _ ) ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left ( by linarith [ hs₁ ( sizeA x ), hs₁' x ] ) _ ) ) )

/-! ## Lab 19, Part 4 — Example: 3-Colouring ≤ₚ 4-Colouring -/

/-- A finite simple graph: vertices are `0, …, n-1`, edges are pairs
with endpoints `< n`. -/
structure WFGraph where
  /-- Number of vertices; the vertices are `0, …, n-1`. -/
  n : ℕ
  /-- The edge list (each edge an unordered pair, stored as an ordered
  pair). -/
  edges : List (ℕ × ℕ)
  /-- Well-formedness: every edge connects two genuine vertices. -/
  wf : ∀ e ∈ edges, e.1 < n ∧ e.2 < n

/-- Size of a graph instance: vertices plus edges. -/
def WFGraph.size (G : WFGraph) : ℕ := G.n + G.edges.length

/-- `c` is a proper `k`-colouring of `G`: it uses colours `< k` on the
vertices and gives adjacent vertices different colours. -/
def ProperColoring (G : WFGraph) (k : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ v, v < G.n → c v < k) ∧ (∀ e ∈ G.edges, c e.1 ≠ c e.2)

/-- `G` is `k`-colourable. -/
def Colorable (G : WFGraph) (k : ℕ) : Prop := ∃ c : ℕ → ℕ, ProperColoring G k c

/-- The reduction map: add an **apex** vertex `G.n` adjacent to every
original vertex. -/
def addApex (G : WFGraph) : WFGraph where
  n := G.n + 1
  edges := G.edges ++ (List.range G.n).map (fun v => (v, G.n))
  wf := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact ⟨lt_trans (G.wf e h).1 (Nat.lt_succ_self _), lt_trans (G.wf e h).2 (Nat.lt_succ_self _)⟩
    · rcases List.mem_map.1 h with ⟨v, hv, rfl⟩
      exact ⟨lt_trans (List.mem_range.1 hv) (Nat.lt_succ_self _), Nat.lt_succ_self _⟩

/-- **Given**: forward direction — a proper 3-colouring of `G` extends
to a proper 4-colouring of `addApex G`. Played (re-derived) in the "Three
to Four Colours" level; supplied here so `addApex_correct` can cite it. -/
theorem addApex_of_threeColorable (G : WFGraph) (h : Colorable G 3) :
    Colorable (addApex G) 4 := by
  obtain ⟨ c, hc ⟩ := h;
  refine' ⟨ fun v => if v < G.n then c v else 3, _, _ ⟩ <;> simp_all +decide only [ProperColoring, ne_eq, Prod.forall];
  · intro v hv
    split_ifs with hvn
    · exact Nat.lt_trans (hc.1 v hvn) (by norm_num)
    · norm_num
  · intro a b hab
    simp only [addApex, List.mem_append, List.mem_map, List.mem_range] at hab
    rcases hab with hab | ⟨v, hv, heq⟩
    · rw [if_pos (G.wf (a, b) hab).1, if_pos (G.wf (a, b) hab).2]
      exact hc.2 a b hab
    · obtain ⟨rfl, rfl⟩ : a = v ∧ b = G.n := by
        rw [Prod.ext_iff] at heq; exact ⟨heq.1.symm, heq.2.symm⟩
      rw [if_pos hv, if_neg (by omega)]
      exact Nat.ne_of_lt (hc.1 a hv)

/-- **Given**: backward direction — a proper 4-colouring of `addApex G`
restricts to a proper 3-colouring of `G`. Played (re-derived) in the
"Three to Four Colours" level; supplied here so `addApex_correct` can
cite it. -/
theorem threeColorable_of_addApex (G : WFGraph) (h : Colorable (addApex G) 4) :
    Colorable G 3 := by
  obtain ⟨ c, hc ⟩ := h;
  obtain ⟨a, ha⟩ : ∃ a, c G.n = a ∧ a < 4 := by
    exact ⟨ _, rfl, hc.1 _ ( Nat.lt_succ_self _ ) ⟩;
  set r : ℕ → ℕ := fun x => if x < a then x else x - 1
  use fun v => r (c v);
  constructor <;> intro v hv <;> simp_all +decide only [ProperColoring, ne_eq, Prod.forall];
  · have hcv : c v < 4 := hc.1 v (by have : (addApex G).n = G.n + 1 := rfl; omega)
    have hne : c v ≠ a := by
      have hmem : (v, G.n) ∈ (addApex G).edges :=
        List.mem_append_right _ (List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩)
      have := hc.2 v G.n hmem; rw [ha.1] at this; exact this
    have ha2 := ha.2
    show (if c v < a then c v else c v - 1) < 3
    split_ifs <;> omega
  · have hw := G.wf v hv
    have h_distinct : c v.1 ≠ c v.2 ∧ c v.1 ≠ a ∧ c v.2 ≠ a := by
      refine ⟨hc.2 _ _ (List.mem_append_left _ hv), ?_, ?_⟩
      · have := hc.2 _ _ (List.mem_append_right _
          (List.mem_map.mpr ⟨v.1, List.mem_range.mpr hw.1, rfl⟩))
        rw [ha.1] at this; exact this
      · have := hc.2 _ _ (List.mem_append_right _
          (List.mem_map.mpr ⟨v.2, List.mem_range.mpr hw.2, rfl⟩))
        rw [ha.1] at this; exact this
    obtain ⟨hd1, hd2, hd3⟩ := h_distinct
    have hb1 : c v.1 < 4 := hc.1 v.1 (by have : (addApex G).n = G.n + 1 := rfl; omega)
    have hb2 : c v.2 < 4 := hc.1 v.2 (by have : (addApex G).n = G.n + 1 := rfl; omega)
    have ha2 := ha.2
    show ¬ (if c v.1 < a then c v.1 else c v.1 - 1) = (if c v.2 < a then c v.2 else c v.2 - 1)
    split_ifs <;> omega

/-- Answer preservation for the apex reduction. -/
theorem addApex_correct (G : WFGraph) : Colorable G 3 ↔ Colorable (addApex G) 4 :=
  ⟨addApex_of_threeColorable G, threeColorable_of_addApex G⟩

/-- **Given**: polynomial (indeed linear) size blow-up of the apex
reduction. Played (re-derived) in the "Three to Four Colours" level;
supplied here so `threeCol_reduces_fourCol` can cite it. -/
theorem addApex_size (G : WFGraph) : (addApex G).size ≤ 3 * (G.size + 1) := by
  unfold WFGraph.size addApex
  simp only [List.length_append, List.length_map, List.length_range]
  omega

/-- **3-Colouring reduces to 4-Colouring in polynomial time.** -/
theorem threeCol_reduces_fourCol :
    PolyReducible WFGraph.size WFGraph.size
      (fun G => Colorable G 3) (fun G => Colorable G 4) :=
  PolyReducible.of_map addApex (fun m => 3 * (m + 1)) (IsPolyBounded.linear 3)
    addApex_correct addApex_size

/-! ## Lab 19, Part 5 — Example: Partition ≤ₚ Subset-Sum ("q-Sum") -/

/-- The sum of the entries of `w` selected by the boolean mask `m`. -/
def selSum (m : List Bool) (w : List ℕ) : ℕ :=
  (List.zipWith (fun b x => if b then x else 0) m w).sum

/-- **Partition**: is there a subset of `w` summing to exactly half the
total? -/
def PartitionProblem (w : List ℕ) : Prop :=
  ∃ m : List Bool, m.length = w.length ∧ 2 * selSum m w = w.sum

/-- A Subset-Sum instance: a list of weights and a target. -/
structure SubsetSumInst where
  /-- The weights. -/
  weights : List ℕ
  /-- The target sum. -/
  target : ℕ

/-- **Subset-Sum / q-Sum**: is there a sub-collection of the weights
summing to the target? -/
def SubsetSum (I : SubsetSumInst) : Prop :=
  ∃ m : List Bool, m.length = I.weights.length ∧ selSum m I.weights = I.target

/-- Size of a Partition instance. -/
def partSize (w : List ℕ) : ℕ := w.length + w.sum

/-- Size of a Subset-Sum instance. -/
def ssSize (I : SubsetSumInst) : ℕ := I.weights.length + I.weights.sum + I.target

/-- The reduction: aim at half the total, unless the total is odd. -/
def partToSS (w : List ℕ) : SubsetSumInst :=
  if w.sum % 2 = 0 then ⟨w, w.sum / 2⟩ else ⟨[], 1⟩

/-- **Given**: answer preservation for the partition reduction. Played
(re-derived) in the "Partition to Sum" level; supplied here so
`partition_reduces_subsetSum` can cite it. -/
theorem partToSS_correct (w : List ℕ) : PartitionProblem w ↔ SubsetSum (partToSS w) := by
  by_cases h : w.sum % 2 = 0 <;> simp_all +decide only [PartitionProblem, SubsetSum, partToSS, ↓reduceIte, Nat.mod_two_not_eq_zero, one_ne_zero, List.length_nil, List.length_eq_zero_iff, exists_eq_left, iff_false, not_exists, not_and];
  · constructor
    · rintro ⟨m, hlen, heq⟩; exact ⟨m, hlen, by omega⟩
    · rintro ⟨m, hlen, heq⟩; exact ⟨m, hlen, by omega⟩
  · intro x _ heq; omega

/-- **Given**: polynomial size blow-up of the partition reduction.
Needed by `partition_reduces_subsetSum`. -/
theorem partToSS_size (w : List ℕ) : ssSize (partToSS w) ≤ 3 * (partSize w + 1) := by
  unfold ssSize partToSS partSize;
  split_ifs <;> simp only [List.length_nil, List.sum_nil] <;> omega

/-- **Partition reduces to Subset-Sum in polynomial time.** -/
theorem partition_reduces_subsetSum :
    PolyReducible partSize ssSize PartitionProblem SubsetSum :=
  PolyReducible.of_map partToSS (fun m => 3 * (m + 1)) (IsPolyBounded.linear 3)
    partToSS_correct partToSS_size

/-! ## Lab 19, Part 6 — Example: Independent-Set ≤ₚ Vertex-Cover -/

/-- `S` is an independent set of `G`. -/
def IsIndep (G : WFGraph) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range G.n ∧ ∀ e ∈ G.edges, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

/-- `C` is a vertex cover of `G`. -/
def IsVC (G : WFGraph) (C : Finset ℕ) : Prop :=
  C ⊆ Finset.range G.n ∧ ∀ e ∈ G.edges, e.1 ∈ C ∨ e.2 ∈ C

/-- **Independent-Set** decision problem. -/
def IndepSet (I : WFGraph × ℕ) : Prop := ∃ S, IsIndep I.1 S ∧ I.2 ≤ S.card

/-- **Vertex-Cover** decision problem. -/
def VertexCover (I : WFGraph × ℕ) : Prop := ∃ C, IsVC I.1 C ∧ C.card ≤ I.2

/-- Size of a graph+threshold instance. -/
def gkSize (I : WFGraph × ℕ) : ℕ := I.1.size + I.2

/-- A fixed vertex-cover no-instance: one edge, budget `0`. -/
def falseVCInst : WFGraph × ℕ := (⟨2, [(0, 1)], by decide⟩, 0)

/-- The reduction: `IndepSet ≥ k` becomes `VertexCover ≤ n - k` (or a
no-instance if `k > n`). -/
def indepToVC (I : WFGraph × ℕ) : WFGraph × ℕ :=
  if I.2 ≤ I.1.n then (I.1, I.1.n - I.2) else falseVCInst

/-- **Given**: complementation — for `S ⊆ V`, `S` is independent iff
`V \ S` is a vertex cover. Played (re-derived) in the "Vertex Cover Complement"
level; supplied here so `indepToVC_correct` can cite it. -/
theorem isIndep_iff_isVC_compl (G : WFGraph) (S : Finset ℕ) (hS : S ⊆ Finset.range G.n) :
    IsIndep G S ↔ IsVC G (Finset.range G.n \ S) := by
  constructor <;> intro h;
  · constructor;
    · exact Finset.sdiff_subset;
    · intro e he; have := h.2 e he; by_cases he1 : e.1 ∈ S <;> by_cases he2 : e.2 ∈ S <;> simp_all +decide only [Finset.subset_iff, Finset.mem_range, and_self, not_true_eq_false, and_false, not_false_eq_true, Finset.mem_sdiff, and_true, false_or, gt_iff_lt, or_false] ;
      · exact G.wf e he |>.2;
      · exact G.wf e he |>.1;
      · exact Or.inl ( G.wf e he |>.1 );
  · refine ⟨hS, fun e he hcon => ?_⟩
    rcases h.2 e he with hmem | hmem <;> rw [Finset.mem_sdiff] at hmem
    · exact hmem.2 hcon.1
    · exact hmem.2 hcon.2

/-- **Given**: the fixed no-instance is genuinely a no-instance. Needed
by `indepToVC_correct`. -/
theorem not_vertexCover_falseVCInst : ¬ VertexCover falseVCInst := by
  rintro ⟨C, hC₁, hC₂⟩
  have hCe : C = ∅ := Finset.card_eq_zero.mp (nonpos_iff_eq_zero.mp hC₂)
  have hmem : (0 : ℕ) ∈ C ∨ (1 : ℕ) ∈ C := hC₁.2 (0, 1) (by simp [falseVCInst])
  simp [hCe] at hmem

/-- **Given**: answer preservation for the independent-set reduction.
Needed by `indepSet_reduces_vertexCover`. -/
theorem indepToVC_correct (I : WFGraph × ℕ) : IndepSet I ↔ VertexCover (indepToVC I) := by
  unfold indepToVC;
  split_ifs <;> simp_all +decide only [VertexCover, not_le];
  · constructor <;> intro h;
    · obtain ⟨ S, hS₁, hS₂ ⟩ := h;
      refine' ⟨ Finset.range I.1.n \ S, _, _ ⟩;
      · exact isIndep_iff_isVC_compl _ _ hS₁.1 |>.1 hS₁;
      · rw [Finset.card_sdiff_of_subset hS₁.1, Finset.card_range]; omega
    · obtain ⟨ C, hC₁, hC₂ ⟩ := h;
      use Finset.range I.1.n \ C;
      simp_all +decide only [IsVC, Prod.forall, IsIndep, Finset.sdiff_subset, Finset.mem_sdiff, Finset.mem_range, not_and, Decidable.not_not, and_imp, true_and];
      refine ⟨fun a b hab _ haC _ => (hC₁.2 a b hab).resolve_left haC, ?_⟩
      rw [Finset.card_sdiff_of_subset hC₁.1, Finset.card_range]; omega
  · constructor <;> intro h;
    · obtain ⟨ S, hS₁, hS₂ ⟩ := h; have := Finset.card_le_card hS₁.1; simp_all +decide only [Finset.card_range] ;
      linarith;
    · exact absurd h ( by rintro ⟨ C, hC₁, hC₂ ⟩ ; exact not_vertexCover_falseVCInst ⟨ C, hC₁, hC₂ ⟩ )

/-- **Given**: polynomial size blow-up of the independent-set reduction.
Needed by `indepSet_reduces_vertexCover`. -/
theorem indepToVC_size (I : WFGraph × ℕ) : gkSize (indepToVC I) ≤ 3 * (gkSize I + 1) := by
  have hn : I.1.n ≤ I.1.size := by unfold WFGraph.size; omega
  unfold gkSize indepToVC
  split_ifs
  · dsimp only; omega
  · have h3 : falseVCInst.1.size + falseVCInst.2 = 3 := by decide
    omega

/-- **Independent-Set reduces to Vertex-Cover in polynomial time.** -/
theorem indepSet_reduces_vertexCover :
    PolyReducible gkSize gkSize IndepSet VertexCover :=
  PolyReducible.of_map indepToVC (fun m => 3 * (m + 1)) (IsPolyBounded.linear 3)
    indepToVC_correct indepToVC_size

/-! ## Lab 20, Part 1 — Decision problems and the classes P and NP -/

/-- A decision problem: a yes/no predicate `pred` on inputs of type
`Input`, with an input-size measure `size`. -/
structure DecisionProblem where
  /-- The type of instances. -/
  Input : Type
  /-- The size measure used to state polynomial time bounds. -/
  size  : Input → ℕ
  /-- The yes/no question. -/
  pred  : Input → Prop

/-- `L ∈ P`: the problem is decided by a polynomial-time solver. -/
def inP (L : DecisionProblem) : Prop :=
  PolyTimeSolvable L.size L.pred

/-- `L ∈ NP`: there is a polynomial-time **verifier** with polynomially
bounded certificates. -/
def inNP (L : DecisionProblem) : Prop :=
  ∃ (Cert : Type) (encSize : Cert → ℕ)
    (verify : L.Input → Cert → TimeM ℕ Bool) (p t : ℕ → ℕ),
    IsPolyBounded p ∧ IsPolyBounded t ∧
    (∀ x, L.pred x ↔ ∃ c, encSize c ≤ p (L.size x) ∧ (verify x c).ret = true) ∧
    (∀ x c, encSize c ≤ p (L.size x) → (verify x c).time ≤ t (L.size x))

/-- The class **P** of polynomial-time decidable problems. -/
def P : Set DecisionProblem := {L | inP L}

/-- The class **NP** of problems with polynomial-time verifiers. -/
def NP : Set DecisionProblem := {L | inNP L}

/-! ## Lab 20, Part 2 — P ⊆ NP -/

/-- **Given**: `P ⊆ NP` — every polynomial-time decidable problem has a
polynomial-time verifier (take the certificate type to be `Unit`, and run
the solver on the input). Played (re-derived) in the "P and NP" level;
supplied here so `P_le_NP` can cite it. -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  obtain ⟨solve, t, ht, hsolve⟩ := hL
  use Unit, fun _ => 0, fun x _ => solve x, fun _ => 0, t
  exact ⟨IsPolyBounded.const 0, ht, fun x => by aesop, fun x c _ => hsolve.2 x⟩

/-! ## Lab 20, Part 3 — Reductions transport membership -/

/-- A polynomial-time many-one reduction between decision problems. -/
def Reduces (A B : DecisionProblem) : Prop :=
  PolyReducible A.size B.size A.pred B.pred

/-- **Given**: if `A` reduces to `B` and `B ∈ P`, then `A ∈ P`. Played
(re-derived) in the "P and NP" level; supplied here in case a later
section needs it. -/
theorem inP_of_reduces {A B : DecisionProblem} (h : Reduces A B) (hB : inP B) : inP A :=
  PolyTimeSolvable.of_reducible h hB

/-- **Given**: if `A` reduces to `B` and `B ∈ NP`, then `A ∈ NP`. Played
(re-derived) in the "P and NP" level; supplied here in case a later
section needs it. -/
theorem inNP_of_reduces {A B : DecisionProblem} (h : Reduces A B) (hB : inNP B) : inNP A := by
  obtain ⟨f, red, t, s, ht, hs, hred₁, hred₂, hred₃, hred₄⟩ := h
  obtain ⟨Cert, encSize, verify, p, t, hp, ht, h₁, h₂⟩ := hB
  rcases hp with ⟨c₁, k₁, hp⟩
  rcases ht with ⟨c₂, k₂, ht⟩
  rcases hs with ⟨c₃, k₃, hs⟩
  refine' ⟨Cert, encSize, fun x c => _, fun n => c₁ * (c₃ * (n + 1) ^ k₃ + 1) ^ k₁,
    fun n => c₂ * (c₃ * (n + 1) ^ k₃ + 1) ^ k₂, _, _, _, _⟩
  exact let y := f x; if h : encSize c ≤ p (B.size y) then verify y c else ⟨Bool.false, 0⟩
  · refine' ⟨c₁ * (c₃ + 1) ^ k₁, k₃ * k₁, fun n => _⟩
    rw [mul_assoc, pow_mul]
    rw [← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith [pow_pos (Nat.succ_pos n) k₃]) _)
  · refine' ⟨c₂ * (c₃ + 1) ^ k₂, k₃ * k₂, fun n => _⟩
    rw [mul_assoc, pow_mul]
    rw [← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith [pow_pos (Nat.succ_pos n) k₃]) _)
  · intro x; specialize hred₂ x; specialize h₁ (f x); simp_all +decide
    constructor <;> rintro ⟨c, hc₁, hc₂⟩
    · exact ⟨c, le_trans hc₁ (le_trans (hp _) (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by linarith [hred₄ x, hs (A.size x)]) _))), by aesop⟩
    · grind
  · intro x c hc; by_cases h : encSize c ≤ p (B.size (f x)) <;> simp +decide [h]
    exact le_trans (h₂ _ _ h) (ht _ |> le_trans <| Nat.mul_le_mul_left _ <|
      Nat.pow_le_pow_left (by linarith [hred₄ x, hs (A.size x)]) _)

/-! ## Lab 20, Part 4 — Closure of P under complement -/

/-- The complement of a problem: same inputs and size, negated
predicate. -/
def compl (L : DecisionProblem) : DecisionProblem :=
  { Input := L.Input, size := L.size, pred := fun x => ¬ L.pred x }

/-- **Given**: `P` is closed under complement — negate the solver's
Boolean output, which costs one extra step and keeps the running time
polynomially bounded. Played (re-derived) in the "Complement Closure"
level; supplied here in case a later section needs it. -/
theorem inP_compl {L : DecisionProblem} (hL : inP L) : inP (compl L) := by
  obtain ⟨solve, t, ht, hcorr, htime⟩ := hL
  refine' ⟨fun x => ⟨!(solve x |> TimeM.ret), (solve x |> TimeM.time)⟩, t, ht, _, _⟩ <;> simp_all +decide
  · intro x; specialize hcorr x; cases h : (solve x |> TimeM.ret) <;> aesop
  · exact htime

/-! ## Phase 6 expansion — NP-completeness, coNP, SAT, and graph complements -/

/-- A problem is NP-hard when every problem in NP reduces to it. -/
def NPHard (target : DecisionProblem) : Prop :=
  ∀ source, inNP source → Reduces source target

/-- A problem is NP-complete when it belongs to NP and is NP-hard. -/
def NPComplete (problem : DecisionProblem) : Prop :=
  inNP problem ∧ NPHard problem

/-- The class coNP consists of complements of NP problems. -/
def inCoNP (problem : DecisionProblem) : Prop :=
  inNP (compl problem)

/-- **Given**: complementing both ends of a many-one reduction preserves
reducibility. Played in the "Complement Reductions" level. -/
def reduceComplements {source target : DecisionProblem}
    (h : Reduces source target) : Reduces (compl source) (compl target) := by
  rcases h with ⟨f, red, time, growth, htime, hgrowth, hret, hcorrect, hrun, hsize⟩
  exact ⟨f, red, time, growth, htime, hgrowth, hret,
    fun x => not_congr (hcorrect x), hrun, hsize⟩

/-- A compact propositional-formula language for the SAT levels. -/
inductive Formula where
  | atom (name : Nat)
  | falsum
  | conj (left right : Formula)
  | disj (left right : Formula)
  | neg (body : Formula)
  deriving DecidableEq

namespace Formula

/-- Evaluate a formula under a Boolean assignment. -/
def eval (assignment : Nat → Bool) : Formula → Bool
  | atom name => assignment name
  | falsum => false
  | conj left right => eval assignment left && eval assignment right
  | disj left right => eval assignment left || eval assignment right
  | neg body => !(eval assignment body)

/-- A formula is satisfiable when some assignment makes it true. -/
def Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Nat → Bool, eval assignment formula = true

end Formula

/-- Literals used by the small 3-CNF model. -/
structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

namespace Literal

/-- Evaluate a positive or negative literal. -/
def eval (assignment : Nat → Bool) (literal : Literal) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

end Literal

/-- A three-literal clause. Repetition allows fewer than three distinct
literals. -/
abbrev Clause3 := Literal × Literal × Literal

/-- A 3-CNF formula is a conjunction represented by a list of
three-literal clauses. -/
abbrev CNF3 := List Clause3

/-- Evaluate one three-literal clause. -/
def evalClause3 (assignment : Nat → Bool) (clause : Clause3) : Bool :=
  clause.1.eval assignment || clause.2.1.eval assignment || clause.2.2.eval assignment

/-- Evaluate a 3-CNF formula. -/
def evalCNF3 (assignment : Nat → Bool) (formula : CNF3) : Bool :=
  formula.all (evalClause3 assignment)

/-- Satisfiability for 3-CNF formulas. -/
def Satisfiable3 (formula : CNF3) : Prop :=
  ∃ assignment : Nat → Bool, evalCNF3 assignment formula = true

/-- A finite undirected graph, represented by a symmetric irreflexive
edge relation on a finite vertex type. -/
structure FiniteGraph where
  vertices : Type
  finiteVertices : Fintype vertices
  decidableEqVertices : DecidableEq vertices
  edge : vertices → vertices → Prop
  decidableEdge : DecidableRel edge
  edge_symm : Symmetric edge
  edge_irrefl : Std.Irrefl edge

attribute [instance] FiniteGraph.finiteVertices FiniteGraph.decidableEqVertices
  FiniteGraph.decidableEdge

namespace FiniteGraph

/-- A vertex set is independent when no two of its members are adjacent. -/
def Independent (graph : FiniteGraph) (set : Finset graph.vertices) : Prop :=
  ∀ ⦃u⦄, u ∈ set → ∀ ⦃v⦄, v ∈ set → ¬ graph.edge u v

/-- A vertex set is a clique when every two distinct members are adjacent. -/
def Clique (graph : FiniteGraph) (set : Finset graph.vertices) : Prop :=
  ∀ ⦃u⦄, u ∈ set → ∀ ⦃v⦄, v ∈ set → u ≠ v → graph.edge u v

/-- A vertex cover meets every edge. -/
def VertexCover (graph : FiniteGraph) (set : Finset graph.vertices) : Prop :=
  ∀ ⦃u v⦄, graph.edge u v → u ∈ set ∨ v ∈ set

/-- The complement graph. -/
def complement (graph : FiniteGraph) : FiniteGraph where
  vertices := graph.vertices
  finiteVertices := graph.finiteVertices
  decidableEqVertices := graph.decidableEqVertices
  edge u v := u ≠ v ∧ ¬ graph.edge u v
  decidableEdge := inferInstance
  edge_symm := by
    intro u v h
    exact ⟨h.1.symm, fun hvu => h.2 (graph.edge_symm hvu)⟩
  edge_irrefl := ⟨by
    intro u h
    exact h.1 rfl⟩

end FiniteGraph

/-- An abstract interface for deterministic and nondeterministic space
classes, with the containments used by the levels. -/
structure SpaceModel where
  L : Set DecisionProblem
  NL : Set DecisionProblem
  PSPACE : Set DecisionProblem
  deterministicLog_is_nondeterministicLog : L ⊆ NL
  nondeterministicLog_is_polynomialSpace : NL ⊆ PSPACE

/-! ## Lab 20, Part 5 — The P versus NP question -/

/-- The **P versus NP** question, as a proposition. Its truth value is
currently unknown; it is stated here, deliberately with no proof
obligation. -/
def PequalsNP : Prop := P = NP

/-- The provable half of the P vs NP question. -/
theorem P_le_NP : P ⊆ NP := P_subset_NP

/-- The open half of the P vs NP question, stated as a proposition
(unknown truth value). -/
def NP_subset_P_conjecture : Prop := NP ⊆ P

/-! ## Lab 20, Part 6 — Savitch's theorem via bounded reachability -/

section Savitch
variable {V : Type*} (step : V → V → Prop)

/-- `LazyWalk step n u v`: there is a walk of length exactly `n` from `u`
to `v` in which each step either stays put or follows `step`. -/
def LazyWalk (n : ℕ) (u v : V) : Prop :=
  ∃ f : ℕ → V, f 0 = u ∧ f n = v ∧ ∀ i, i < n → (f i = f (i + 1) ∨ step (f i) (f (i + 1)))

/-- **Given**: `LazyWalk step 0 u v` holds iff `u = v`. Needed by
`reach_zero`. -/
theorem lazyWalk_zero (u v : V) : LazyWalk step 0 u v ↔ u = v := by
  refine' ⟨fun ⟨f, hf₀, hf₁, hf₂⟩ => hf₀.symm.trans hf₁,
    fun h => ⟨fun _ => u, rfl, h.symm ▸ rfl, by simp +decide⟩⟩

/-- **Given**: a lazy walk of length `n` is also one of length `n + 1`.
Needed by `lazyWalk_mono_le`. -/
theorem lazyWalk_mono {n : ℕ} {u v : V} (h : LazyWalk step n u v) : LazyWalk step (n + 1) u v := by
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := h
  use fun i => if i ≤ n then f i else v
  grind

/-- **Given**: lazy walks are monotone in the length bound. Needed by
`reach_iff_reachable`. -/
theorem lazyWalk_mono_le {n m : ℕ} {u v : V} (hnm : n ≤ m) (h : LazyWalk step n u v) :
    LazyWalk step m u v := by
      obtain ⟨p, hp⟩ := h
      use fun i => if i ≤ n then p i else p n
      grind

/-- **Given**: concatenation/splitting of lazy walks — the combinatorial
heart of the halving recursion. Played (re-derived) in the "Reachability
Split" level; supplied here so `reach_succ` can cite it. -/
theorem lazyWalk_add {n m : ℕ} {u v : V} :
    LazyWalk step (n + m) u v ↔ ∃ w, LazyWalk step n u w ∧ LazyWalk step m w v := by
      constructor
      · rintro ⟨f, hf⟩
        refine' ⟨f n, ⟨fun i => f (Min.min i n), _, _, _⟩, ⟨fun i => f (n + i), _, _, _⟩⟩ <;>
          simp_all +decide; all_goals grind
      · rintro ⟨w, hw₁, hw₂⟩
        obtain ⟨f, hf₁, hf₂, hf₃⟩ := hw₁
        obtain ⟨g, hg₁, hg₂, hg₃⟩ := hw₂
        use fun i => if i ≤ n then f i else g (i - n)
        grind

/-- **Given**: a lazy walk witnesses reachability. Needed by
`reach_iff_reachable`. -/
theorem lazyWalk_to_reflTransGen {n : ℕ} {u v : V} (h : LazyWalk step n u v) :
    Relation.ReflTransGen step u v := by
      obtain ⟨f, hf₀, hf₁, hf₂⟩ := h
      rw [← hf₀, ← hf₁]
      have h_ind : ∀ j ≤ n, Relation.ReflTransGen step (f 0) (f j) := by
        intro j hj
        induction' j with j ih
        · rfl
        · cases hf₂ j (Nat.lt_of_succ_le hj) <;>
            [exact ‹f j = f (j + 1)› ▸ ih (Nat.le_of_succ_le hj);
             exact Relation.ReflTransGen.tail (ih (Nat.le_of_succ_le hj)) ‹_›]
      exact h_ind n le_rfl

/-- **Given**: conversely, reachability gives a lazy walk of some length.
Needed by `reach_iff_reachable`. -/
theorem reflTransGen_to_lazyWalk {u v : V} (h : Relation.ReflTransGen step u v) :
    ∃ n, LazyWalk step n u v := by
      induction' h with u v huv ih
      · exact ⟨0, ⟨fun _ => u, rfl, rfl, by simp +decide⟩⟩
      · have h_combined : ∃ n, LazyWalk step n u v := by
          exact ⟨1, fun i => if i = 0 then u else v, rfl, rfl, by simp +decide [ih]⟩
        obtain ⟨m, hm⟩ := h_combined
        exact Exists.elim ‹∃ n, LazyWalk step n _ _› fun n hn =>
          ⟨n + m, by rw [lazyWalk_add] ; exact ⟨u, hn, hm⟩⟩

/-- **Given**: pigeonhole shrinking — in a finite configuration graph,
any lazy walk can be shortened to one of length at most `Fintype.card V`.
Needed by `reach_iff_reachable`. -/
theorem lazyWalk_card [Fintype V] {n : ℕ} {u v : V} (h : LazyWalk step n u v) :
    LazyWalk step (Fintype.card V) u v := by
      revert h
      induction' n using Nat.strong_induction_on with n ih generalizing u v
      by_cases hn : n ≤ Fintype.card V
      · grind +suggestions
      · intro h
        obtain ⟨f, hf0, hfn, hf_step⟩ := h
        have h_repeat : ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
          by_contra! h
          exact absurd (Fintype.card_le_of_injective (fun i : Fin (n + 1) => f i) fun i j hij =>
            le_antisymm (not_lt.1 fun hi => h _ _ hi (by linarith [Fin.is_lt i, Fin.is_lt j]) hij.symm)
              (not_lt.1 fun hj => h _ _ hj (by linarith [Fin.is_lt i, Fin.is_lt j]) hij))
            (by simpa using by linarith)
        obtain ⟨i, j, hij, hjn, h⟩ := h_repeat
        have h_walk : LazyWalk step (n - (j - i)) u v := by
          refine' ⟨fun k => if k ≤ i then f k else f (k + (j - i)), _, _, _⟩ <;> simp +decide [*]
          · grind
          · intro k hk; split_ifs <;> simp_all +decide
            · exact hf_step k (by omega)
            · cases le_antisymm ‹_› ‹_›; simp_all +decide [Nat.succ_add]
              simpa [add_tsub_cancel_of_le hij.le] using hf_step j (by omega)
            · linarith
            · grind
        grind +splitImp

/-- **Savitch's bounded-reachability predicate.** `reach step k u v`
means `v` is reachable from `u` within `2^k` steps. -/
def reach (k : ℕ) (u v : V) : Prop := LazyWalk step (2 ^ k) u v

/-- **Given**: base case of the halving recursion — within `2^0 = 1`
step, `v` is reachable from `u` iff `u = v` or `step u v`. Needed by
`reach_succ`. -/
theorem reach_zero (u v : V) : reach step 0 u v ↔ (u = v ∨ step u v) := by
  constructor
  · rintro ⟨f, hf₀, hf₁, hf₂⟩
    grind
  · rintro (rfl | h)
    · exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
    · exact ⟨fun i => if i = 0 then u else v, rfl, rfl, fun i hi => by cases i <;> tauto⟩

/-- **Given**: the halving recursion at the heart of Savitch — `reach`
within `2^(k+1)` steps holds iff there is a midpoint `m` reachable within
`2^k` steps that itself reaches `v` within `2^k` steps. Played
(re-derived) in the "Reachability Split" level; supplied here in case a
later section needs it. -/
theorem reach_succ (k : ℕ) (u v : V) :
    reach step (k + 1) u v ↔ ∃ m, reach step k u m ∧ reach step k m v := by
      rw [reach]
      rw [pow_succ', two_mul, lazyWalk_add]
      rfl

/-- **Given**: correctness of the halving recursion — if `2^k` is at
least the number of configurations, `reach step k` decides reachability
exactly. Played (re-derived) in the "Savitch's Theorem" level; supplied here
so `savitch_reachability` can cite it. -/
theorem reach_iff_reachable [Fintype V] (k : ℕ) (h : Fintype.card V ≤ 2 ^ k) (u v : V) :
    reach step k u v ↔ Relation.ReflTransGen step u v := by
      constructor
      · intro h_walk
        apply lazyWalk_to_reflTransGen
        exact h_walk
      · intro h
        have h_card : LazyWalk step (Fintype.card V) u v := by
          obtain ⟨w, hw⟩ := reflTransGen_to_lazyWalk _ h
          exact lazyWalk_card _ hw
        exact lazyWalk_mono_le _ (by linarith) h_card

/-- **Savitch (reachability form).** Taking the recursion depth
`k = ⌈log₂ N⌉`, the halving recursion `reach` decides reachability. -/
theorem savitch_reachability [Fintype V] (u v : V) :
    reach step (Nat.clog 2 (Fintype.card V)) u v ↔ Relation.ReflTransGen step u v :=
  reach_iff_reachable step _ (Nat.le_pow_clog (by norm_num) _) u v

end Savitch

/-- The working space of Savitch's algorithm on an `N`-configuration
graph. -/
def savitchSpace (N : ℕ) : ℕ := Nat.clog 2 N * Nat.clog 2 N

/-- **Given**: the Savitch space bound is `(⌈log₂ N⌉)² = O(log² N)`. Not
needed elsewhere, but recorded for completeness. -/
theorem savitchSpace_eq (N : ℕ) : savitchSpace N = (Nat.clog 2 N) ^ 2 := by
  rw [savitchSpace, sq]

/-! ## Lab 21, Part 2 — Closure properties of computable predicates -/

/-- **Given**: computable predicates are closed under **negation**.
Played (re-derived) in the "Computable Closure" level; supplied here in
case a later section needs it. -/
theorem Computable_not {α : Type*} [Primcodable α] {p : α → Prop} (hp : ComputablePred p) :
    ComputablePred (fun a => ¬ p a) :=
  hp.not

/-- **Given**: computable predicates are closed under **conjunction**.
Played (re-derived) in the "Computable Closure" level; supplied here in
case a later section needs it. -/
theorem Computable_and {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun a => p a ∧ q a) := by
      obtain ⟨_, hp⟩ := hp
      obtain ⟨_, hq⟩ := hq
      refine' ⟨inferInstance, _⟩
      convert Computable.cond (hp) (hq) (Computable.const false) using 1
      funext a; rw [Bool.decide_and]; cases hp : decide (p a) <;> rfl

/-- **Given**: computable predicates are closed under **disjunction**.
Played (re-derived) in the "Computable Closure" level; supplied here in
case a later section needs it. -/
theorem Computable_or {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun a => p a ∨ q a) := by
      obtain ⟨_, hpc⟩ := hp
      obtain ⟨_, hqc⟩ := hq
      use by infer_instance
      convert Computable.cond hpc (Computable.const true) hqc using 1
      funext a; rw [Bool.decide_or]; cases hp : decide (p a) <;> rfl

/-! ## Lab 21, Part 3 — The halting problem -/

/-- **Given**: the halting problem is undecidable — for every fixed
input `n`, the set of codes that halt on `n` is not computable. Not
played directly, but cited (specialised at `n = 0`) by Lab 22's Busy
Beaver principle. -/
theorem halting_undecidable (n : ℕ) : ¬ ComputablePred (fun c : Nat.Partrec.Code => (c.eval n).Dom) :=
  ComputablePred.halting_problem n

/-- **Given**: the halting set is recursively enumerable. Not needed
elsewhere, but recorded for completeness. -/
theorem halting_re (n : ℕ) : REPred (fun c : Nat.Partrec.Code => (c.eval n).Dom) :=
  ComputablePred.halting_problem_re n

/-- **Given**: the halting set's complement is not r.e. Not needed
elsewhere, but recorded for completeness. -/
theorem halting_compl_not_re (n : ℕ) : ¬ REPred (fun c : Nat.Partrec.Code => ¬ (c.eval n).Dom) :=
  ComputablePred.halting_problem_not_re n

/-! ## Lab 21, Part 5 — Rice's theorem -/

/-- **Given**: Rice's theorem, index form — a behaviour-invariant set of
codes `C` is computable iff it is empty or everything. Needed by
`rice_nontrivial`. -/
theorem rice_index (C : Set Nat.Partrec.Code)
    (H : ∀ cf cg : Nat.Partrec.Code, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ :=
  ComputablePred.rice₂ C H

/-- **Given**: Rice's theorem, semantic form. Not needed by
`rice_nontrivial`'s proof directly, but recorded since it is the more
commonly cited form of Rice's theorem. -/
theorem rice_semantic (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c : Nat.Partrec.Code => c.eval ∈ C)
    {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C :=
  ComputablePred.rice C h hf hg fC

/-! ## Lab 21, Part 6 — The boundary: a decidable syntactic property -/

/-- **Given**: a purely syntactic property is decidable — "is `c`
literally the code `Code.zero`?". Played (re-derived) in the "Syntactic
Escape" level; supplied here in case a later section needs it. -/
theorem syntactic_decidable : ComputablePred (fun c : Nat.Partrec.Code => c = Nat.Partrec.Code.zero) := by
  have h_decidable : DecidablePred (fun c : Nat.Partrec.Code => c = Nat.Partrec.Code.zero) := by
    exact fun c => Classical.propDecidable _
  refine' ⟨h_decidable, _⟩
  convert Computable.of_eq _ _
  exact fun c => match c with | Nat.Partrec.Code.zero => Bool.true | _ => Bool.false
  · convert Computable.nat_casesOn (Computable.id) _ _
    rotate_left
    exact Bool
    exact inferInstance
    exact fun _ => Bool.true
    exact fun _ _ => Bool.false
    · exact Computable.const Bool.true
    · exact Computable.const false
    · constructor <;> intro h
      · convert Computable.nat_casesOn (Computable.id) _ _ using 1
        · exact Computable.const true
        · exact Computable.const false
      · convert h.comp (Computable.encode) using 1
        ext (_ | _ | _ | _ | _ | _) <;> rfl
  · intro n; cases n <;> simp

/-! ## Lab 21, Part 7 — Model independence -/

/-- **Given**: model independence — a function `ℕ →. ℕ` is `Nat.Partrec`
iff it is the behaviour of some program code `c`. Played (re-derived) in
the "Model Independence" level; supplied here in case a later section needs
it. -/
theorem model_independence (f : ℕ →. ℕ) : Nat.Partrec f ↔ ∃ c : Nat.Partrec.Code, c.eval = f :=
  Nat.Partrec.Code.exists_code

/-! ## Lab 22, Part 0 — Recalling the halting problem -/

/-- **The halting problem on blank input**, reused verbatim from Lab 21:
the set of codes that halt on input `0` is not computable. Needed by
`busy_beaver_principle`. -/
theorem halting_on_zero_undecidable :
    ¬ ComputablePred (fun c : Nat.Partrec.Code => (c.eval 0).Dom) :=
  halting_undecidable 0

/-! ## Lab 22, Part 1 — Exact halting time of a single program -/

/-- The **halting time** of `c` on input `0`: the least number of steps
after which `evaln` reports an answer, or `0` if the program never
halts. -/
noncomputable def haltTime (c : Nat.Partrec.Code) : ℕ :=
  if h : ∃ k, (Nat.Partrec.Code.evaln k c 0).isSome then Nat.find h else 0

/-- **Given**: correctness of `haltTime` — if `c` halts on input `0`,
running it for exactly `haltTime c` steps already produces an answer.
Played (re-derived) in the "Exact Halt Time" level; supplied here so
`bbSteps_not_computable` can cite it. -/
theorem haltTime_spec {c : Nat.Partrec.Code} (h : (c.eval 0).Dom) :
    (Nat.Partrec.Code.evaln (haltTime c) c 0).isSome := by
  have hex : ∃ k, (Nat.Partrec.Code.evaln k c 0).isSome := by
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
    rw [Nat.Partrec.Code.evaln_complete] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hk]; rfl⟩
  rw [haltTime, dif_pos hex]
  exact Nat.find_spec hex

/-- **Given**: monotonicity of the bounded evaluator (packaged) — once a
program has halted within `k` steps, it has halted within any larger
budget. Played (re-derived) in the "Exact Halt Time" level; supplied here
so `bbSteps_not_computable`/`bbSteps_dominates` can cite it. -/
theorem evaln_isSome_mono {c : Nat.Partrec.Code} {k N : ℕ}
    (hk : (Nat.Partrec.Code.evaln k c 0).isSome) (hN : k ≤ N) :
    (Nat.Partrec.Code.evaln N c 0).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
  have : x ∈ Nat.Partrec.Code.evaln N c 0 := Nat.Partrec.Code.evaln_mono hN (by rw [hx]; rfl)
  rw [Option.mem_def] at this
  rw [this]; rfl

/-! ## Lab 22, Part 2 — The Busy Beaver step function -/

/-- The **Busy Beaver step function**: the maximum halting time among
all programs whose code number is at most `n`. -/
noncomputable def bbSteps (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (fun m =>
    match (Encodable.decode m : Option Nat.Partrec.Code) with
    | some c => haltTime c
    | Option.none => 0)

/-- **Given**: every program's halting time is recorded by `bbSteps` at
its own code number. Played (re-derived) in the "Busy Beaver Bound"
level; supplied here so `bbSteps_not_computable` can cite it. -/
theorem haltTime_le_bbSteps (c : Nat.Partrec.Code) : haltTime c ≤ bbSteps (Encodable.encode c) := by
  have hmem : Encodable.encode c ∈ Finset.range (Encodable.encode c + 1) := by simp
  refine le_trans ?_ (Finset.le_sup (f := (fun m =>
    match (Encodable.decode m : Option Nat.Partrec.Code) with
    | some c => haltTime c
    | Option.none => 0)) hmem)
  simp only [Encodable.encodek, le_refl]

/-! ## Lab 22, Part 3 — The Busy Beaver principle -/

/-- **Given**: the Busy Beaver principle — no computable function bounds
the halting time of every program (a direct reduction from the halting
problem). Played (re-derived) in the "Busy Beaver Has No Computable Bound" level; supplied here so
`bbSteps_not_computable` can cite it. -/
theorem busy_beaver_principle :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧
      ∀ c : Nat.Partrec.Code, (c.eval 0).Dom →
        (Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0).isSome := by
  rintro ⟨f, hf, hbound⟩
  apply halting_on_zero_undecidable
  have hg : Computable (fun c : Nat.Partrec.Code =>
      (Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0).isSome) := by
    have h1 : Computable (fun c : Nat.Partrec.Code => f (Encodable.encode c)) :=
      hf.comp Computable.encode
    have h3 : Computable (fun c : Nat.Partrec.Code =>
        Nat.Partrec.Code.evaln (f (Encodable.encode c)) c 0) :=
      (Nat.Partrec.Code.primrec_evaln.to_comp).comp
        ((h1.pair Computable.id).pair (Computable.const 0))
    exact Primrec.option_isSome.to_comp.comp h3
  refine ComputablePred.computable_iff.2 ⟨_, hg, funext fun c => propext ?_⟩
  exact ⟨fun hdom => hbound c hdom, fun hs => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
    exact Part.dom_iff_mem.2 ⟨x, Nat.Partrec.Code.evaln_sound (by rw [hx]; rfl)⟩⟩

/-! ## Lab 22, Part 4 — Consequences: uncomputability -/

/-- **Given**: the Busy Beaver step function is uncomputable — if it
were, it would itself be a computable upper bound on halting times,
contradicting `busy_beaver_principle`. Played (re-derived) in the "Final
Boss" level; supplied here in case a later section needs it. -/
theorem bbSteps_not_computable : ¬ Computable bbSteps := by
  intro h
  exact busy_beaver_principle ⟨bbSteps, h,
    fun c hdom => evaln_isSome_mono (haltTime_spec hdom) (haltTime_le_bbSteps c)⟩

/-! ## Phase 7 expansion — many-one reductions and semidecidability -/

/-- A **many-one reduction** from `source` to `target`: a total
computable map preserving yes/no answers exactly. -/
def ManyOne {α β : Type*} [Primcodable α] [Primcodable β]
    (source : α → Prop) (target : β → Prop) : Prop :=
  ∃ f : α → β, Computable f ∧ ∀ x, source x ↔ target (f x)

/-- **Given**: pulling a computable predicate back along a computable map
preserves computability. Needed by `undecidable_of_manyOne`. -/
theorem computable_preimage {α β : Type*} [Primcodable α] [Primcodable β]
    {p : β → Prop} {f : α → β} (hp : ComputablePred p) (hf : Computable f) :
    ComputablePred (fun x => p (f x)) := by
  simp_all +decide [ComputablePred]
  obtain ⟨ g, hg ⟩ := hp
  exact ⟨ inferInstance, hg.comp hf ⟩

/-- **Given**: undecidability transports forward along a many-one
reduction. Played in the "Undecidability Transport" level; supplied here
so later levels can cite the packaged preimage argument directly. -/
theorem undecidable_of_manyOne {α β : Type*} [Primcodable α] [Primcodable β]
    {source : α → Prop} {target : β → Prop}
    (hred : ManyOne source target) (hsource : ¬ ComputablePred source) :
    ¬ ComputablePred target := by
  intro htarget
  obtain ⟨f, hf, hcorr⟩ := hred
  have hpreimage : ComputablePred (fun x => target (f x)) := by
    exact computable_preimage htarget hf
  have hsource' : ComputablePred source := by
    rw [show source = fun x => target (f x) from funext fun x => propext (hcorr x)]
    exact hpreimage
  exact hsource hsource'

/-- A predicate is **semi-decidable** when its yes-instances are
recursively enumerable. -/
abbrev SemiDecidable {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  REPred p

/-- A predicate is **co-semi-decidable** when its no-instances are
recursively enumerable. -/
def CoSemiDecidable {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  REPred (fun x => ¬ p x)

/-- **Given**: a behaviour-invariant, nontrivial property of program
codes is undecidable. This packages `rice_index` into the form used by
the Totality/Emptiness/Equivalence levels. -/
theorem rice_nontrivial {C : Set Nat.Partrec.Code}
    (invariant : ∀ cf cg : Nat.Partrec.Code, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C))
    {yes no : Nat.Partrec.Code} (hyes : yes ∈ C) (hno : no ∉ C) :
    ¬ ComputablePred (fun c => c ∈ C) := by
  intro hcomp
  rcases (rice_index C invariant).mp hcomp with hempty | huniv
  · rw [hempty] at hyes
    simp at hyes
  · rw [huniv] at hno
    exact hno (Set.mem_univ no)

/-- The property that a program halts on every input. -/
def Total (c : Nat.Partrec.Code) : Prop :=
  ∀ n, (c.eval n).Dom

/-- The property that a program computes the nowhere-defined partial
function. -/
def Empty (c : Nat.Partrec.Code) : Prop :=
  c.eval = fun _ => Part.none

/-- Extensional equivalence with a fixed base program. -/
def EquivalentTo (base c : Nat.Partrec.Code) : Prop :=
  c.eval = base.eval

/-- **Given**: a constant program halts on every input. Used as a
yes-witness for `Total`. -/
theorem const_total (value : ℕ) : Total (Nat.Partrec.Code.const value) := by
  intro n
  simp

/-- **Given**: there exists a program that diverges on every input. Used
as an emptiness witness. -/
theorem exists_empty_code : ∃ c : Nat.Partrec.Code, Empty c := by
  convert Nat.Partrec.Code.exists_code.mp Nat.Partrec.none

/-- **Given**: the constant-zero program is not empty. Used as a
counterexample for `Empty`. -/
theorem const_zero_not_empty : ¬ Empty (Nat.Partrec.Code.const 0) := by
  intro h
  have := congrFun h 0
  simp at this

/-- **Given**: the constant-zero and constant-one programs are not
extensionally equivalent. Used to obtain a no-witness for
`EquivalentTo base`. -/
theorem const_zero_ne_const_one :
    (Nat.Partrec.Code.const 0).eval ≠ (Nat.Partrec.Code.const 1).eval := by
  intro h
  have := congrFun h 0
  simp +decide at this

end Game.Complexity
