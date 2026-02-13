

theorem P3_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X] {f : ι → Set X}
    (h : ∀ i, Topology.P3 (f i)) : Topology.P3 (⋃ i, f i) := by
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (f i)) := (h i) hxi
  have h_mono : interior (closure (f i)) ⊆ interior (closure (⋃ i, f i)) := by
    have h_subset : closure (f i) ⊆ closure (⋃ j, f j) := by
      have h_sub : f i ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_subset
  exact h_mono hx_int