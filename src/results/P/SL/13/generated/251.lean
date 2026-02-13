

theorem Topology.interior_closure_closure_interior_eq_interior_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (closure (interior (A : Set X)))) =
      interior (closure (interior A)) := by
  simpa [closure_closure]