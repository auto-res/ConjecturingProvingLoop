

theorem Topology.IsOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  simpa using (Topology.IsOpen_P1_and_P3 (A := A) hA).2