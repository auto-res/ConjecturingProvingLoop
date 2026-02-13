

theorem Topology.P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure A) := by
  intro hDense
  have hEq : closure (closure A) = (Set.univ : Set X) := by
    simpa [closure_closure] using hDense.closure_eq
  simpa using
    (Topology.P3_of_closure_eq_univ (A := closure A) hEq)