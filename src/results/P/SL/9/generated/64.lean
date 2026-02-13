

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, Topology.P1 (A := 𝒜 i)) :
    Topology.P1 (A := ⋃ i, 𝒜 i) := by
  dsimp [Topology.P1] at *
  intro x hx_union
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hx_i⟩
  have hx_closure : x ∈ closure (interior (𝒜 i)) := h𝒜 i hx_i
  have h_subset :
      closure (interior (𝒜 i)) ⊆ closure (interior (⋃ j, 𝒜 j)) := by
    have h_int_subset : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
      have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_set_subset
    exact closure_mono h_int_subset
  exact h_subset hx_closure