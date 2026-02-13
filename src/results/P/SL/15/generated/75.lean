

theorem dense_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure A) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have h_closure_eq : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [closure_closure, h_closure_eq, interior_univ] using this