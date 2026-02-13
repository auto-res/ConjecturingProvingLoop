

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, interior (𝒜 i)) ⊆ interior (⋃ i, 𝒜 i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
    have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_set_subset
  exact h_subset hx_i