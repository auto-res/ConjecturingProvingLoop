

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1]
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP1A := h𝒜 A hA_mem
  have hxClA : x ∈ closure (interior A) := hP1A hxA
  have hInt_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have hSub : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
    exact interior_mono hSub
  have hCl_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hInt_subset
  exact hCl_subset hxClA