

theorem Topology.P3_sUnion_isOpen {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → IsOpen A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hOpen
  -- Upgrade the openness assumption to `P3` for every set in `𝒜`.
  have hP3 : ∀ A, A ∈ 𝒜 → Topology.P3 A := by
    intro A hA
    exact Topology.P3_of_isOpen (A := A) (hOpen A hA)
  -- Apply the existing `P3_sUnion` lemma.
  exact Topology.P3_sUnion (X := X) (𝒜 := 𝒜) hP3