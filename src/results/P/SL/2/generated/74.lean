

theorem Topology.dense_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure (A : Set X)) := by
  intro hDense
  intro x _
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense.closure_eq, interior_univ, closure_closure] using this