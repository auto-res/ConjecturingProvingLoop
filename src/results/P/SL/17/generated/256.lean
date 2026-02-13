

theorem Topology.closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x ∈ closure (interior A)`
  have hxA : x ∈ closure (interior A) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior A := by
      intro y hy; exact hy.1
    exact (closure_mono h_subset) hx
  -- Show `x ∈ closure (interior B)`
  have hxB : x ∈ closure (interior B) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy; exact hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hxA hxB