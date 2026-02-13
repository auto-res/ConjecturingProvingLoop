

theorem Topology.P3_sUnion_of_P2 {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hP2
  have hP3 : ∀ A, A ∈ 𝒜 → Topology.P3 A := by
    intro A hA
    exact Topology.P2_implies_P3 (A := A) (hP2 A hA)
  exact Topology.P3_sUnion (X := X) (𝒜 := 𝒜) hP3