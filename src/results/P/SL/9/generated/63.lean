

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, Topology.P2 (A := 𝒜 i)) :
    Topology.P2 (A := ⋃ i, 𝒜 i) := by
  dsimp [Topology.P2] at *
  intro x hx_union
  -- Pick an index `i` such that `x ∈ 𝒜 i`.
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hx_i⟩
  -- Apply `P2` for this particular set.
  have hx_int : x ∈ interior (closure (interior (𝒜 i))) := h𝒜 i hx_i
  -- Show that this interior is contained in the required one.
  have h_subset :
      interior (closure (interior (𝒜 i))) ⊆
        interior (closure (interior (⋃ j, 𝒜 j))) := by
    -- `interior` is monotone with respect to set inclusion.
    have h_int_mono : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
      have h_set_subset : (𝒜 i) ⊆ ⋃ j, 𝒜 j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_set_subset
    -- Apply monotonicity of `closure` and `interior` successively.
    have h_closure_mono :
        closure (interior (𝒜 i)) ⊆ closure (interior (⋃ j, 𝒜 j)) :=
      closure_mono h_int_mono
    exact interior_mono h_closure_mono
  exact h_subset hx_int