

theorem open_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → IsOpen A := by
  intro hP3
  exact (Topology.P3_iff_open_of_closed (A := A) hClosed).1 hP3