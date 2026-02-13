

theorem P2_sUnion_of_P2
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 (A : Set X)) :
    Topology.P2 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P2` for the particular set `A`.
  have hx_intA : x ∈ interior (closure (interior (A : Set X))) :=
    (h𝒜 A hA_mem) hxA
  -- Show that this interior is contained in the target interior.
  have hIncl :
      closure (interior (A : Set X)) ⊆
        closure (interior (⋃₀ 𝒜 : Set X)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have hIntIncl :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (⋃₀ 𝒜 : Set X))) :=
    interior_mono hIncl
  exact hIntIncl hx_intA