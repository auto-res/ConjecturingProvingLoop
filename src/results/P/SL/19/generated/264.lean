

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure (interior A)))))))) =
      interior (closure (interior A)) := by
  simp [Topology.interior_closure_interior_closure_eq_interior_closure,
        closure_closure, interior_interior]