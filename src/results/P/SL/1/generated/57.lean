

theorem Topology.P3_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure A) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have hEq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [closure_closure, hEq, interior_univ] using this