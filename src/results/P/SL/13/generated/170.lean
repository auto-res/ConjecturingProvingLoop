

theorem Topology.closure_interior_closure_interior_closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  have h :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (interior A)) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior
        (X := X) (A := interior A))
  simpa [interior_interior] using h