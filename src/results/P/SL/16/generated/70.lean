

theorem Topology.closed_P3_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) :
    interior A = A := by
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  simpa using hOpen.interior_eq