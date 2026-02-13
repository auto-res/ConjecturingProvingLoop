

theorem Topology.dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 A := by
  intro hDense
  intro x _
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense.closure_eq, interior_univ] using this