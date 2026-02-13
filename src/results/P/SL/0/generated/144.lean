

theorem isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → IsOpen (A : Set X) := by
  intro hP2
  simpa using
    ((Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed)).1 hP2