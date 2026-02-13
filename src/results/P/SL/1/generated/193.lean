

theorem Topology.isClopen_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) : IsClopen A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_P2_of_isClosed (A := A) hClosed hP2
  exact ⟨hClosed, hOpen⟩