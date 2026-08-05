import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Heap"
Level 1
Title "Heap Invariant"
-- source: RequestProject Lab15.merge_isHeap

Introduction "A **(max-)heap** always makes its largest element cheaply
available, via one invariant: every element is `≤` the key at the root of
its subtree. The one primitive `merge` fuses two heaps by comparing their
roots and recursively merging into the larger one. Prove `merge`
*maintains* the invariant — the centrepiece every later operation builds
on."

Statement {a b : Heap} (ha : IsHeap a) (hb : IsHeap b) : IsHeap (merge a b) := by
  Hint "Strong-induct on the combined size `size a + size b`, case on both heaps' shape, and
  split on which root is kept."
  have h_ind : ∀ (s : ℕ), (∀ (a b : Heap), size a + size b < s → IsHeap a → IsHeap b → IsHeap (merge a b)) →
      ∀ (a b : Heap), size a + size b = s → IsHeap a → IsHeap b → IsHeap (merge a b) := by
    rintro s ih a b rfl ha hb
    rcases a with (_ | ⟨l₁, x₁, r₁⟩) <;> rcases b with (_ | ⟨l₂, x₂, r₂⟩) <;> simp_all +decide
    unfold merge
    split_ifs <;> simp_all +decide [isHeap_node_iff]
    · Hint (hidden := true) "The new root is `x₁`; every element of `merge r₁ (node l₂ x₂ r₂)`
      is `≤ x₁`, via `elems_merge` and the case hypotheses."
      intro y hy
      have hy2 := (elems_merge r₁ (l₂.node x₂ r₂)).mem_iff.mp hy
      rw [List.mem_append, elems, List.mem_cons, List.mem_append] at hy2
      rcases hy2 with h | h | h | h
      · exact ha.2.1 y h
      · exact le_of_eq_of_le h ‹x₂ ≤ x₁›
      · exact le_trans (hb.1 y h) ‹x₂ ≤ x₁›
      · exact le_trans (hb.2.1 y h) ‹x₂ ≤ x₁›
    · Hint (hidden := true) "Symmetric case, new root `x₂`; the recursive call is discharged
      by the strong-induction hypothesis `ih`."
      refine' ⟨_, ih _ _ _ _ _⟩
      · intro y hy
        have hy2 := (elems_merge r₂ (l₁.node x₁ r₁)).mem_iff.mp hy
        rw [List.mem_append, elems, List.mem_cons, List.mem_append] at hy2
        have hx : x₁ ≤ x₂ := ‹x₁ < x₂›.le
        rcases hy2 with h | h | h | h
        · exact hb.2.1 y h
        · exact le_of_eq_of_le h hx
        · exact le_trans (ha.1 y h) hx
        · exact le_trans (ha.2.1 y h) hx
      · simp +arith +decide [size]
      · tauto
      · exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2⟩
  have h_ind : ∀ (s : ℕ), ∀ (a b : Heap), size a + size b = s → IsHeap a → IsHeap b → IsHeap (merge a b) := by
    intro s
    induction' s using Nat.strong_induction_on with s ih
    exact h_ind s (fun a b hab ha hb => ih _ hab a b rfl ha hb)
  exact h_ind _ _ _ rfl ha hb

Conclusion "Verified: merging two heaps yields a heap."

NewDefinition Game.Clockwork.Heap Game.Clockwork.Heap.nil Game.Clockwork.Heap.node
  Game.Clockwork.elems Game.Clockwork.IsHeap
  Game.Clockwork.merge
NewTheorem Game.Clockwork.isHeap_node_iff Game.Clockwork.elems_merge
  List.Perm.mem_iff List.mem_append le_of_eq_of_le
