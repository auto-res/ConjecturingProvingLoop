

theorem Topology.P2_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen S) :
    Topology.P2 (⋃₀ 𝒜) := by
  -- Each open set in `𝒜` satisfies `P2`.
  have hP2 : ∀ S : Set X, S ∈ 𝒜 → Topology.P2 S := by
    intro S hS
    exact Topology.isOpen_implies_P2 (X := X) (A := S) (h𝒜 S hS)
  -- Apply the sUnion lemma for `P2`.
  exact Topology.P2_sUnion (X := X) (𝒜 := 𝒜) hP2