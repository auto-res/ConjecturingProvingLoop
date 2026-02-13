

theorem Topology.closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]