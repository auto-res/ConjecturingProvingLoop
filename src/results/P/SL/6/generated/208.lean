

theorem P3_sUnion_of_P3
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 (A : Set X)) :
    Topology.P3 (⋃₀ 𝒜 : Set X) := by
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  -- Choose a witness set `A ∈ 𝒜` such that `x ∈ A`.
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P3` for this particular set `A`.
  have hx_intA : x ∈ interior (closure (A : Set X)) :=
    (h𝒜 A hA_mem) hxA
  -- Show that `interior (closure A)` is contained in the desired interior.
  have hIncl :
      closure (A : Set X) ⊆ closure (⋃₀ 𝒜 : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have hIntIncl :
      interior (closure (A : Set X)) ⊆
        interior (closure (⋃₀ 𝒜 : Set X)) :=
    interior_mono hIncl
  exact hIntIncl hx_intA