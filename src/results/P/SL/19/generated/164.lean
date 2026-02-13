

set_option maxRecDepth 10000

theorem Topology.closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure A) = closure A := by
  simpa [closure_closure]