

theorem P1_closure_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP1 : Topology.P1 A := Topology.P1_of_open (A := A) hA
  exact Topology.P1_closure_of_P1 (A := A) hP1