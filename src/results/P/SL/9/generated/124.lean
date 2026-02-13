

theorem Topology.iUnion_closure_subset_closure_iUnion {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, closure (𝒜 i)) ⊆ closure (⋃ i, 𝒜 i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_subset : closure (𝒜 i) ⊆ closure (⋃ j, 𝒜 j) :=
    closure_mono h_subset
  exact h_closure_subset hx_i