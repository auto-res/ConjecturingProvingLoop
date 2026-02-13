

theorem Topology.interior_sUnion_of_open {X : Type*} [TopologicalSpace X]
    {𝒞 : Set (Set X)} (h𝒞 : ∀ s, s ∈ 𝒞 → IsOpen (s : Set X)) :
    interior (⋃₀ 𝒞 : Set X) = ⋃₀ 𝒞 := by
  have hOpen : IsOpen (⋃₀ 𝒞 : Set X) := isOpen_sUnion h𝒞
  simpa using hOpen.interior_eq