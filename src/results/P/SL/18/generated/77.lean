

theorem P1_iff_P2_of_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_open_closure_interior hP1 hOpen
  · intro hP2
    exact Topology.P2_implies_P1 hP2