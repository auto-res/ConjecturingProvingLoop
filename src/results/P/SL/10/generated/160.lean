

theorem Topology.closure_closure_interior_closure_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (closure (interior (closure A))) = closure (interior (closure A)) := by
  simpa using
    (Topology.closure_closure_interior (X := X) (A := closure A))