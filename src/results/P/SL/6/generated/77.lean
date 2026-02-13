

theorem open_closure_implies_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure (A : Set X)) := by
  simpa using
    (Topology.open_satisfies_P2 (A := closure (A : Set X)) hOpen)