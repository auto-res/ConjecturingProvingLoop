

theorem Topology.interior_closure_interior_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior A))) = interior (closure (interior A)) := by
  simpa [interior_interior]