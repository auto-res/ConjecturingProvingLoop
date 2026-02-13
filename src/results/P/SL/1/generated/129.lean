

theorem Topology.P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure A) := by
  intro hDense
  have hEq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [hEq] using (P1_univ (X := X))