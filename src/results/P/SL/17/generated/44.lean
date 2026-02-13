

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h
  unfold Topology.P3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := h A hA_mem
  have hx₁ : x ∈ interior (closure A) := hP3A hxA
  have hsubset_closure : closure A ⊆ closure (⋃₀ 𝒜) :=
    closure_mono (Set.subset_sUnion_of_mem hA_mem)
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono hsubset_closure
  exact hsubset hx₁