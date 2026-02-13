

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro h
  unfold Topology.P1
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := h A hA_mem
  have hx₁ : x ∈ closure (interior A) := hP1A hxA
  have hsubset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have hA_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
    exact interior_mono hA_subset
  have hclosure : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset
  exact hclosure hx₁