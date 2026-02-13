

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Show `x ∈ closure A`.
  have hxA : x ∈ closure A := by
    -- `A ∩ interior B ⊆ A`.
    have h_sub : (A ∩ interior B : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono h_sub) hx
  -- Show `x ∈ closure B`.
  have hxB : x ∈ closure B := by
    -- `interior B ⊆ B`.
    have h_int_subset : (interior B : Set X) ⊆ B := interior_subset
    -- Hence `A ∩ interior B ⊆ B`.
    have h_sub : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact h_int_subset hy.2
    exact (closure_mono h_sub) hx
  exact And.intro hxA hxB