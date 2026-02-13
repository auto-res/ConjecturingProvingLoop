

theorem isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 A → IsOpen (A : Set X) := by
  intro hP3
  have hEquiv :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  exact (hEquiv).1 hP3