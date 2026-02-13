

theorem interior_closure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.interior_closure_nonempty_of_P3 hP3 hA