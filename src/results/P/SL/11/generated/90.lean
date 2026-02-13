

theorem P1_iff_P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_open_closure (A := A) hP1 hOpenCl
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2