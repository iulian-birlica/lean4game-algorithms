import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "SortingTheory"
Level 4
Title "Decision Tree Leaves"
-- source: RequestProject Lab13.numLeaves_le_two_pow_height, Lab13.factorial_le_numLeaves

Introduction "A comparison sort traces out a binary decision tree: each
comparison is an internal node, each stopping point a leaf outputting a
permutation. Prove the two combinatorial bounds behind the lower bound:
a tree of height `h` has at most `2^h` leaves (shape), and a tree that
sorts needs at least `n!` leaves (information)."

Statement {n : ℕ} (t : DTree n) (h : Sorts t) :
    numLeaves t ≤ 2 ^ height t ∧ n.factorial ≤ numLeaves t := by
  Hint "Prove the shape bound by induction on `t`; the information bound
  assembles from the supplied `outputs_card_le_numLeaves`/`run_mem_outputs`
  cards."
  constructor
  · clear h
    induction' t with i j l r ihl ihr
    · simp only [numLeaves, height, pow_zero, le_refl]
    · Hint (hidden := true) "The step case combines both induction hypotheses with
      `pow_le_pow_right₀` on whichever subtree is taller."
      simp +arith +decide [*, height]
      exact le_trans (add_le_add ihr ‹_›) (by rw [pow_succ']; exact by cases max_cases (height r) (height ihl) <;> linarith [pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by linarith : height r ≤ max (height r) (height ihl)), pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by linarith : height ihl ≤ max (height r) (height ihl))])
  · Hint (hidden := true) "Every permutation's inverse is an output, and the output-count
    card bounds the leaf count."
    refine' le_trans _ (outputs_card_le_numLeaves t)
    have h_image : Finset.image (fun σ : Equiv.Perm (Fin n) => σ⁻¹) Finset.univ ⊆ outputs t := by
      exact Finset.image_subset_iff.mpr fun σ _ => h σ ▸ run_mem_outputs σ t
    exact le_trans (by rw [Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy]; simp +decide [Fintype.card_perm]) (Finset.card_mono h_image)

Conclusion "Verified: both combinatorial bounds behind the comparison-sort lower bound."

NewDefinition Game.Clockwork.DTree Game.Clockwork.DTree.leaf
  Game.Clockwork.DTree.node Game.Clockwork.numLeaves Game.Clockwork.height
  Game.Clockwork.Sorts Game.Clockwork.outputs Fin Equiv.Perm Finset.univ
  Finset.image
NewTheorem Game.Clockwork.outputs_card_le_numLeaves Game.Clockwork.run_mem_outputs
  add_le_add pow_le_pow_right₀ max_cases Finset.image_subset_iff Finset.card_image_of_injective
  Fintype.card_perm Finset.card_mono
