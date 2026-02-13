

theorem Topology.interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior A)))) = interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_idempotent (A := interior A))