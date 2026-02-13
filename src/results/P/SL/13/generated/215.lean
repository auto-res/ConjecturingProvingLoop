

theorem Topology.closure_interior_iterate_eight_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))) =
      closure (interior A) := by
  simp [Topology.closure_interior_closure_interior_eq_closure_interior,
        Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure,
        closure_closure]