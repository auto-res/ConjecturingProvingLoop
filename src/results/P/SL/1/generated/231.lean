

theorem Topology.isOpen_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure A) := by
  intro hDense
  have hEq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  simpa [hEq] using isOpen_univ