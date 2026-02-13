

theorem Topology.P1_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen S) :
    Topology.P1 (⋃₀ 𝒜) := by
  -- Every open set satisfies `P1`.
  have hP1 : ∀ S : Set X, S ∈ 𝒜 → Topology.P1 S := by
    intro S hS
    exact Topology.isOpen_implies_P1 (X := X) (A := S) (h𝒜 S hS)
  -- Apply the existing `P1` lemma for countable unions.
  exact Topology.P1_sUnion (X := X) (𝒜 := 𝒜) hP1