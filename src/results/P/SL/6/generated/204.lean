

theorem P1_sUnion_of_P1
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 (A : Set X)) :
    Topology.P1 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  -- Find a set `A ∈ 𝒜` that contains `x`.
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P1` for this particular set `A`.
  have hA_P1 : Topology.P1 (A : Set X) := h𝒜 A hA_mem
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA_P1 hxA
  -- Show that the closure of `interior A` is contained in the closure of
  -- `interior (⋃₀ 𝒜)`.
  have hIncl :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  -- Conclude the desired membership.
  exact hIncl hx_cl