

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A := h𝒜 A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have h_mono : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      have h_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact h_mono hx_closure