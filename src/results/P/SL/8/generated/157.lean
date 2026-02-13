

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3]
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP3A := h𝒜 A hA_mem
  have hxIntA : x ∈ interior (closure A) := hP3A hxA
  have h_closure : closure A ⊆ closure (⋃₀ 𝒜) := by
    have h_sub : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
    exact closure_mono h_sub
  have h_interior :
      interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure
  exact h_interior hxIntA