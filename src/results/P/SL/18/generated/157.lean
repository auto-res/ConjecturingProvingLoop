

theorem isOpen_of_closed_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 A) :
    IsOpen (A : Set X) := by
  exact ((Topology.P2_closed_iff_open (A := A) hClosed).1 hP2)