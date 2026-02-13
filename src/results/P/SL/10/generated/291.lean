

theorem Topology.closure_interior_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  have hxIntA : x ∈ closure (interior A) := by
    have h_subset : interior A ∩ B ⊆ interior A := Set.inter_subset_left
    exact (closure_mono h_subset) hx
  have hxB : x ∈ closure B := by
    have h_subset : interior A ∩ B ⊆ B := Set.inter_subset_right
    exact (closure_mono h_subset) hx
  exact And.intro hxIntA hxB