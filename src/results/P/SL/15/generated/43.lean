

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3]
  intro x hx
  obtain ⟨A, hA_mem, hxA⟩ := Set.mem_sUnion.1 hx
  have hP3A := h𝒜 A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have h_mono : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    have h_subset : closure A ⊆ closure (⋃₀ 𝒜) := by
      have : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact closure_mono this
    exact interior_mono h_subset
  exact h_mono hx_int