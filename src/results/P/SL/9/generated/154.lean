

theorem Topology.closureInteriorClosureInteriorClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_idempotent (A := closure A))