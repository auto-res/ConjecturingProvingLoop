

theorem P1_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  dsimp [Topology.P1]
  simpa [closure_closure, interior_closure_closure_eq]