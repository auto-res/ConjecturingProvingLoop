

theorem Topology.closure_interior_inter_interior_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior A ∩ interior B ⊆ interior A`
  have hx_left : x ∈ closure (interior A) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior A := by
      intro y hy; exact hy.1
    exact (closure_mono h_subset) hx
  -- `interior A ∩ interior B ⊆ interior B`
  have hx_right : x ∈ closure (interior B) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy; exact hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hx_left hx_right