

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h𝒜 A hA_mem
  have hx' : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion_of_mem hy hA_mem
  exact hsubset hx'

theorem exists_open_superset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro _ _; trivial
  · dsimp [Topology.P3]
    intro x hx
    simpa [closure_univ, interior_univ] using hx