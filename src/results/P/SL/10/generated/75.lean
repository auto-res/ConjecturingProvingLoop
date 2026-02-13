

theorem Topology.closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa using
        Topology.closure_interior_closure_interior_eq_closure_interior
          (X := X) (A := closure (interior A))
    _ = closure (interior A) := by
      simpa using
        Topology.closure_interior_closure_interior_eq_closure_interior
          (X := X) (A := A)