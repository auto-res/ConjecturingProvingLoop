

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, Topology.P3 (A := 𝒜 i)) :
    Topology.P3 (A := ⋃ i, 𝒜 i) := by
  dsimp [Topology.P3] at *
  intro x hx_union
  -- Choose an index `i` such that `x ∈ 𝒜 i`.
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hx_i⟩
  -- Apply `P3` for this particular set.
  have hx_int : x ∈ interior (closure (𝒜 i)) := h𝒜 i hx_i
  -- Show this interior is contained in the desired one.
  have h_subset :
      interior (closure (𝒜 i)) ⊆ interior (closure (⋃ j, 𝒜 j)) := by
    -- Monotonicity of `closure`.
    have h_closure_mono :
        closure (𝒜 i) ⊆ closure (⋃ j, 𝒜 j) := by
      have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_set_subset
    -- Apply monotonicity of `interior`.
    exact interior_mono h_closure_mono
  exact h_subset hx_int