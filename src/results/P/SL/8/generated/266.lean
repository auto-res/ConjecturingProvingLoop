

theorem closed_P3_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    exact closed_P3_interior_eq (X := X) (A := A) hA_closed hP3
  · intro hInt
    have hA_open : IsOpen A := by
      simpa [hInt] using (isOpen_interior : IsOpen (interior A))
    exact Topology.isOpen_imp_P3 (X := X) (A := A) hA_open