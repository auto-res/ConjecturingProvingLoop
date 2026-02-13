

theorem Topology.IsOpen_P1_P2_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X)) ∧
      Topology.P2 (closure (A : Set X)) ∧
      Topology.P3 (closure (A : Set X)) := by
  simpa using
    (Topology.IsOpen_P1_P2_P3 (A := closure (A : Set X)) hOpen)