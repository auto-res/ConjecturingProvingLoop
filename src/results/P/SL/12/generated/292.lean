

theorem Topology.closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (A : Set X)) = closure A := by
  simpa [closure_closure]