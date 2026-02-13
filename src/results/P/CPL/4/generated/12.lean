

theorem P2_Union_countable {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (h : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, s n) := by
  simpa using (P2_Union_family (X := X) (s := s) h)

theorem P2_sUnion_directed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hdir : DirectedOn (· ⊆ ·) 𝒜) (h : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  simpa using
    (P2_sUnion_family (ι := Unit) (X := X) (𝒜 := 𝒜) h)