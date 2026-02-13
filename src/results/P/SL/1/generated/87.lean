

theorem Topology.isOpen_of_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A → IsOpen A := by
  intro hP3
  exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3