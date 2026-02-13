

theorem P3_sUnion_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, IsOpen A) : Topology.P3 (⋃₀ 𝒜) := by
  refine P3_sUnion (𝒜 := 𝒜) ?_
  intro A hA
  exact P3_of_open (h𝒜 A hA)