

theorem P1_of_P3_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure A) := by
  exact Topology.P1_of_open_closure (A := A) hOpenCl