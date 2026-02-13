

theorem Topology.closed_P2_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) : interior A = A := by
  have hOpen : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  simpa using hOpen.interior_eq