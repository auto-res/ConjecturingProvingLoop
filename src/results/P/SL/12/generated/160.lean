

theorem Topology.closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closure_interior_closure_interior_eq
      (X := X) (A := closure A))