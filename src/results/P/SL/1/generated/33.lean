

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq] using this