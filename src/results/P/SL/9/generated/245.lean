

theorem Topology.interior_iUnion_eq_iUnion_of_open
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, IsOpen (𝒜 i)) :
    interior (⋃ i, 𝒜 i) = ⋃ i, 𝒜 i := by
  have h_open : IsOpen (⋃ i, 𝒜 i) := isOpen_iUnion (fun i ↦ h𝒜 i)
  simpa using h_open.interior_eq