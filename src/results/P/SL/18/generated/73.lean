

theorem closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_interior_nonempty_of_P1 hP1 hA