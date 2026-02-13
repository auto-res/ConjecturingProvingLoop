

theorem Topology.IsOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  exact (Topology.IsOpen_P1_and_P3 (A := A) hA).1