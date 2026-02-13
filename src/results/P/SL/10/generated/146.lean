

theorem Topology.closure_inter_interiors_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure (interior A) := by
    have h_subset : interior A ∩ interior B ⊆ interior A :=
      Set.inter_subset_left
    exact (closure_mono h_subset) hx
  have hxB : x ∈ closure (interior B) := by
    have h_subset : interior A ∩ interior B ⊆ interior B :=
      Set.inter_subset_right
    exact (closure_mono h_subset) hx
  exact And.intro hxA hxB