

theorem Topology.closure_interior_closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (interior A)))) =
      closure (interior A) := by
  simpa [interior_interior] using
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A))