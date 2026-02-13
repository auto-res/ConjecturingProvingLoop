

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 (X := X) A) :
    Topology.P3 (X := X) (⋃₀ 𝒜) := by
  classical
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hxUnion
  rcases Set.mem_sUnion.1 hxUnion with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure A) := h𝒜 A hA_mem hxA
  have h_closure_subset : closure A ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_int_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure_subset
  exact h_int_subset hxInt