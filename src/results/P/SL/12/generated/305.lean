

theorem Topology.P3_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (closure (A : Set X))) ↔
      Topology.P3 (X := X) (closure A) := by
  simpa [closure_closure]