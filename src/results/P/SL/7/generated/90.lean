

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP2 : Topology.P2 A := Topology.IsOpen_P2 (A := A) hA
  exact Topology.P2_implies_P1_closure (A := A) hP2