

theorem Topology.closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show membership in `closure (interior A)`.
  have hxA : x ∈ closure (interior A) := by
    -- `interior A ∩ interior B ⊆ interior A`.
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior A := by
      intro y hy; exact hy.1
    -- Apply monotonicity of `closure`.
    exact (closure_mono h_subset) hx
  -- Show membership in `closure (interior B)`.
  have hxB : x ∈ closure (interior B) := by
    -- `interior A ∩ interior B ⊆ interior B`.
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy; exact hy.2
    -- Apply monotonicity of `closure`.
    exact (closure_mono h_subset) hx
  -- Combine the two facts.
  exact And.intro hxA hxB