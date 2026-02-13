

theorem Topology.interior_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure (interior A))) = interior (closure (interior A)) := by
  simpa [interior_interior]