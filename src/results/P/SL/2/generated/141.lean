

theorem Topology.dense_interior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 A := by
  intro hDenseInt
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDenseInt.closure_eq, interior_univ] using this