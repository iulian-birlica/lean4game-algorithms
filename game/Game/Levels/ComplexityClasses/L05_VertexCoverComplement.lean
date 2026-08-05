import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 5
Title "Vertex Cover Complement"
-- source: RequestProject Lab19.isIndep_iff_isVC_compl, Lab19.indepSet_reduces_vertexCover

Introduction "An independent set contains no edge; a vertex cover touches every edge — the two
are complementary: `S` is independent iff `V \\ S` is a vertex cover. Prove the complement
fact, then assemble the reduction `IndepSet ≥ k` ↦ `VertexCover ≤ n - k` (or a supplied
no-instance, if `k > n`)."

Statement :
    (∀ (G : WFGraph) (S : Finset ℕ), S ⊆ Finset.range G.n →
      (IsIndep G S ↔ IsVC G (Finset.range G.n \ S))) ∧
    PolyReducible gkSize gkSize IndepSet VertexCover := by
  Hint "Both directions of the complement fact case on whether each edge endpoint is in `S`."
  have hcompl : ∀ (G : WFGraph) (S : Finset ℕ), S ⊆ Finset.range G.n →
      (IsIndep G S ↔ IsVC G (Finset.range G.n \ S)) := by
    intro G S hS
    constructor <;> intro h
    · constructor
      · exact Finset.sdiff_subset
      · intro e he
        have := h.2 e he
        by_cases he1 : e.1 ∈ S <;> by_cases he2 : e.2 ∈ S <;>
          simp_all +decide only [Finset.subset_iff, Finset.mem_range, and_self, not_true_eq_false,
            and_false, not_false_eq_true, Finset.mem_sdiff, and_true, false_or, gt_iff_lt, or_false]
        · exact G.wf e he |>.2
        · exact G.wf e he |>.1
        · exact Or.inl (G.wf e he |>.1)
    · refine ⟨hS, fun e he hcon => ?_⟩
      rcases h.2 e he with hmem | hmem <;> rw [Finset.mem_sdiff] at hmem
      · exact hmem.2 hcon.1
      · exact hmem.2 hcon.2
  refine ⟨hcompl, ?_⟩
  Hint (hidden := true) "Assemble the reduction's answer-preservation fact by hand, citing your
  own `hcompl` exactly where the construction needs the complement fact, splitting on whether
  `k ≤ n` (the supplied `not_vertexCover_falseVCInst` handles the no-instance case), then feed
  it and the supplied `indepToVC_size` to `PolyReducible.of_map`."
  have hcorr : ∀ I : WFGraph × ℕ, IndepSet I ↔ VertexCover (indepToVC I) := by
    intro I
    unfold indepToVC
    split_ifs <;> simp_all +decide only [VertexCover, not_le]
    · constructor <;> intro h
      · obtain ⟨S, hS₁, hS₂⟩ := h
        refine' ⟨Finset.range I.1.n \ S, _, _⟩
        · exact hcompl _ _ hS₁.1 |>.1 hS₁
        · rw [Finset.card_sdiff_of_subset hS₁.1, Finset.card_range]; omega
      · obtain ⟨C, hC₁, hC₂⟩ := h
        use Finset.range I.1.n \ C
        simp_all +decide only [IsVC, Prod.forall, IsIndep, Finset.sdiff_subset,
          Finset.mem_sdiff, Finset.mem_range, not_and, Decidable.not_not, and_imp, true_and]
        refine ⟨fun a b hab _ haC _ => (hC₁.2 a b hab).resolve_left haC, ?_⟩
        rw [Finset.card_sdiff_of_subset hC₁.1, Finset.card_range]; omega
    · constructor <;> intro h
      · obtain ⟨S, hS₁, hS₂⟩ := h
        have := Finset.card_le_card hS₁.1
        simp_all +decide only [Finset.card_range]
        linarith
      · exact absurd h (by rintro ⟨C, hC₁, hC₂⟩; exact not_vertexCover_falseVCInst ⟨C, hC₁, hC₂⟩)
  exact PolyReducible.of_map indepToVC (fun m => 3 * (m + 1)) (IsPolyBounded.linear 3)
    hcorr indepToVC_size

Conclusion "Verified: Independent-Set reduces to Vertex-Cover in polynomial time."

NewDefinition Game.Complexity.IsIndep Game.Complexity.IsVC Game.Complexity.IndepSet
  Game.Complexity.VertexCover Game.Complexity.gkSize Game.Complexity.falseVCInst
  Game.Complexity.indepToVC Finset
NewTheorem Game.Complexity.not_vertexCover_falseVCInst Game.Complexity.indepToVC_size
  Game.Complexity.IsPolyBounded.linear Game.Complexity.PolyReducible.of_map or_false
  not_true_eq_false not_false_eq_true gt_iff_lt Finset.subset_iff Finset.sdiff_subset
  Finset.mem_sdiff Finset.mem_range Finset.card_sdiff_of_subset Finset.card_range
  Finset.card_le_card false_or Decidable.not_not and_true and_imp and_false absurd
