

theorem dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have h_closure : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure, interior_univ]