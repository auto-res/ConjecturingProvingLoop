

theorem Topology.closure_interior_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior (closure A))) = closure (interior (closure A)) := by
  simpa [interior_interior]