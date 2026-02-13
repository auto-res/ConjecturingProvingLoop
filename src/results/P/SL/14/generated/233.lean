

theorem Topology.P3_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen S) :
    Topology.P3 (⋃₀ 𝒜) := by
  -- Each open set in `𝒜` satisfies `P3`.
  have hP3 : ∀ S : Set X, S ∈ 𝒜 → Topology.P3 S := by
    intro S hS
    exact Topology.isOpen_implies_P3 (X := X) (A := S) (h𝒜 S hS)
  -- Apply the union lemma for `P3`.
  exact Topology.P3_sUnion (X := X) (𝒜 := 𝒜) hP3