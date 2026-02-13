

theorem Topology.interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence their interiors satisfy the same relation.
  have hA : (x : X) ∈ interior A := by
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono h_subset) hx
  -- Similarly, `A ∩ B` is contained in `B`.
  have hB : (x : X) ∈ interior B := by
    have h_subset : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (interior_mono h_subset) hx
  exact And.intro hA hB