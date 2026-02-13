

theorem dense_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _
  have hEq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hEq, interior_univ, closure_univ] using this