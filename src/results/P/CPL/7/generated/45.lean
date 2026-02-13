

theorem P3_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsClosed A ∧ Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h
  have hP3 : ∀ A ∈ 𝒜, Topology.P3 A := by
    intro A hA
    exact (h A hA).2
  exact P3_sUnion (𝒜 := 𝒜) hP3