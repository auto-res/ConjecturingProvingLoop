

theorem Topology.iUnion_closureInterior_subset_closureInterior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, closure (interior (𝒜 i))) ⊆
      closure (interior (⋃ i, 𝒜 i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (𝒜 i)` is contained in `interior (⋃ i, 𝒜 i)`.
  have h_int_subset : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
    have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_set_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior (𝒜 i)) ⊆ closure (interior (⋃ j, 𝒜 j)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_i