

theorem Topology.P2_sUnion_isOpen {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → IsOpen A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hOpen
  -- First, upgrade the openness assumption to `P2` for every set in `𝒜`.
  have hP2 : ∀ A, A ∈ 𝒜 → Topology.P2 A := by
    intro A hA
    exact Topology.P2_of_isOpen (A := A) (hOpen A hA)
  -- Apply the existing `P2_sUnion` lemma.
  exact Topology.P2_sUnion (X := X) (𝒜 := 𝒜) hP2