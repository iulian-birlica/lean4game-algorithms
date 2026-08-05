import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 3
Title "Three to Four Colours"
-- source: RequestProject Lab19.addApex_of_threeColorable, Lab19.threeColorable_of_addApex,
--   Lab19.threeCol_reduces_fourCol

Introduction "**3-Colouring reduces to 4-Colouring.** Add a single **apex** vertex joined to
every original vertex: it is forced to take a fourth colour, freeing exactly three colours
for the rest of the graph. Prove both directions of the correctness argument, then assemble
the polynomial-time reduction."

Statement :
    (∀ G : WFGraph, Colorable G 3 → Colorable (addApex G) 4) ∧
    (∀ G : WFGraph, Colorable (addApex G) 4 → Colorable G 3) ∧
    PolyReducible WFGraph.size WFGraph.size (fun G => Colorable G 3) (fun G => Colorable G 4) := by
  Hint "Prove both directions first; the reduction then assembles from `PolyReducible.of_map`,
  fed the two directions (as the answer-preservation iff) and the supplied linear size bound
  `addApex_size`."
  have hfwd : ∀ G : WFGraph, Colorable G 3 → Colorable (addApex G) 4 := by
    intro G h
    obtain ⟨c, hc⟩ := h
    refine' ⟨fun v => if v < G.n then c v else 3, _, _⟩ <;>
      simp_all +decide only [ProperColoring, ne_eq, Prod.forall]
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
  Hint (hidden := true) "The backward direction relabels colours: let `a` be the apex's colour,
  then shift every colour above `a` down by one."
  have hbwd : ∀ G : WFGraph, Colorable (addApex G) 4 → Colorable G 3 := by
    intro G h
    obtain ⟨c, hc⟩ := h
    obtain ⟨a, ha⟩ : ∃ a, c G.n = a ∧ a < 4 := ⟨_, rfl, hc.1 _ (Nat.lt_succ_self _)⟩
    set r : ℕ → ℕ := fun x => if x < a then x else x - 1
    use fun v => r (c v)
    constructor <;> intro v hv <;> simp_all +decide only [ProperColoring, ne_eq, Prod.forall]
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
  refine ⟨hfwd, hbwd, ?_⟩
  exact PolyReducible.of_map addApex (fun m => 3 * (m + 1)) (IsPolyBounded.linear 3)
    (fun G => ⟨hfwd G, hbwd G⟩) addApex_size

Conclusion "Verified: 3-Colouring reduces to 4-Colouring in polynomial time."

NewDefinition Game.Complexity.WFGraph Game.Complexity.ProperColoring Game.Complexity.Colorable
  Game.Complexity.addApex
NewTactic ext set
NewTheorem Game.Complexity.addApex_size Game.Complexity.PolyReducible.of_map
  Game.Complexity.IsPolyBounded.linear Prod.forall Prod.ext_iff ne_eq Nat.ne_of_lt Nat.lt_trans
  Nat.lt_succ_self List.mem_map List.mem_append_right List.mem_append_left
