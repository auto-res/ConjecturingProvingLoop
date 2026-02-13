

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A))))
      = closure (interior (closure A)) := by
  simpa
    [Topology.interior_closure_interior_closure_eq_interior_closure (X := X) (A := A)]