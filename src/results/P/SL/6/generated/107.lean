

theorem open_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → IsOpen A := by
  intro hP2
  exact (Topology.P2_iff_open_of_closed (A := A) hClosed).1 hP2