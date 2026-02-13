

theorem Topology.P1_sUnion_isOpen {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → IsOpen A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hOpen
  -- First, turn the openness assumption into `P1` for every set in `𝒜`.
  have hP1 : ∀ A, A ∈ 𝒜 → Topology.P1 A := by
    intro A hA
    exact Topology.P1_of_isOpen (A := A) (hOpen A hA)
  -- Apply the existing `P1_sUnion` theorem.
  exact Topology.P1_sUnion (X := X) (𝒜 := 𝒜) hP1