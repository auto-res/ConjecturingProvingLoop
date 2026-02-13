

theorem dense_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure A) := by
  intro hDense
  have h_closure_eq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure_eq] using (Topology.P1_univ (X := X))