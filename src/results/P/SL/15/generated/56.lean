

theorem P1_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X] {f : ι → Set X}
    (h : ∀ i, Topology.P1 (f i)) : Topology.P1 (⋃ i, f i) := by
  dsimp [Topology.P1] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_closure : x ∈ closure (interior (f i)) := (h i) hxi
  have h_mono : closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
    have h_int_subset : interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : f i ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact h_mono hx_closure