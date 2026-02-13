

theorem Topology.closure_interior_closure_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) = closure (interior (closure A)) := by
  simpa [closure_closure] using
    (rfl :
      closure (interior (closure (closure A))) =
        closure (interior (closure (closure A))))