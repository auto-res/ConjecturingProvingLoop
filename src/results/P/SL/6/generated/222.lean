

theorem P1_iff_P2_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X)) ↔ Topology.P2 (closure (A : Set X)) := by
  simpa using
    (Topology.P1_iff_P2_of_isOpen (A := closure (A : Set X)) hOpen)