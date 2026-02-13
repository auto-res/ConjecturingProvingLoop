

theorem P3_of_P2_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hOpenCl : IsOpen (closure A)) :
    Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.P3_of_P1_and_open_closure hP1 hOpenCl