

theorem Topology.interior_sUnion_eq_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen (S : Set X)) :
    interior (⋃₀ 𝒜 : Set X) = ⋃₀ 𝒜 := by
  have hOpen : IsOpen (⋃₀ 𝒜 : Set X) := isOpen_sUnion h𝒜
  simpa using hOpen.interior_eq