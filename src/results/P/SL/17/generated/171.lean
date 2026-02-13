

theorem Topology.P2_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  have h_eq : closure (closure A) = closure A := by
    simpa [closure_closure]
  simpa [h_eq]