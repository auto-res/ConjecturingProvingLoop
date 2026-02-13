

theorem open_closure_implies_P1_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X)) := by
  simpa using
    (Topology.open_satisfies_P1 (A := closure (A : Set X)) hOpen)