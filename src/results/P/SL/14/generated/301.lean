

theorem Topology.P3_iff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    exact
      Topology.interior_eq_of_isClosed_and_P3
        (X := X) (A := A) hA_closed hP3
  · intro hInt
    have hOpen : IsOpen A := by
      simpa [hInt] using (isOpen_interior : IsOpen (interior A))
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen