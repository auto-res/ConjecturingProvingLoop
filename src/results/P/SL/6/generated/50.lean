

theorem P2_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  simpa using
    ((Topology.P3_closure_iff_P2_closure (A := A)).symm.trans
      (Topology.P3_closure_iff_open_closure (A := A)))