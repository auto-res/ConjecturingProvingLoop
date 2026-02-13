

theorem open_closure_implies_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 (closure (A : Set X)) := by
  simpa using
    (Topology.open_satisfies_P3 (A := closure (A : Set X)) hOpen)