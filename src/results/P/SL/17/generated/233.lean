

theorem Topology.isOpen_closure_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) : IsOpen (closure A) := by
  have h_eq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  simpa [h_eq] using isOpen_univ