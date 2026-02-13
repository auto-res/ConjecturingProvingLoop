

theorem P2_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsOpen A ∧ P2 A) → P2 (⋃₀ 𝒜) := by
  intro h
  apply P2_sUnion
  intro A hA
  exact (h A hA).2