

theorem Topology.interior_inter_subset_interior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A := by
  intro x hx
  -- Since `A ∩ B ⊆ A`, apply `interior_mono` to obtain the desired inclusion.
  have h_subset : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
  exact (interior_mono h_subset) hx