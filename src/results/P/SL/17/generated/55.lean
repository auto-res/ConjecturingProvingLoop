

theorem Topology.P1_sUnion_of_P2 {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hP2
  -- Derive P1 for every set in 𝒜 from the assumed P2 property
  have hP1 : ∀ A, A ∈ 𝒜 → Topology.P1 A := by
    intro A hA
    exact Topology.P2_implies_P1 (A := A) (hP2 A hA)
  -- Apply the existing `P1_sUnion` theorem
  exact Topology.P1_sUnion (X := X) (𝒜 := 𝒜) hP1