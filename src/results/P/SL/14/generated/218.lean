

theorem Topology.P1_closure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (closure (A : Set X))) ↔ Topology.P1 (closure A) := by
  simpa [closure_closure]