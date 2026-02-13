

theorem Topology.P3_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (closure (A : Set X))) ↔ Topology.P3 (closure A) := by
  simpa [closure_closure]