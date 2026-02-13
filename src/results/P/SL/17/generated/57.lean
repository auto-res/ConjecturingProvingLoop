

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro h
  unfold Topology.P2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h A hA_mem
  have hx₁ : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset_int : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono (Set.subset_sUnion_of_mem hA_mem)
  have hsubset_clos : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset_int
  have hsubset : interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono hsubset_clos
  exact hsubset hx₁