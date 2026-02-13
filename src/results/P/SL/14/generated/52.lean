

theorem Topology.P2_closure_iff_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure A) := by
  simpa using
    (Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).trans
      ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).symm)