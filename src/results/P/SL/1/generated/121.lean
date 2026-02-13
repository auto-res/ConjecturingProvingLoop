

theorem Topology.interior_eq_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
  simpa using hOpen.interior_eq