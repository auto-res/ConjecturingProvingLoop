

theorem Topology.P2_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (closure (A : Set X))) ↔ Topology.P2 (closure A) := by
  simpa [closure_closure]