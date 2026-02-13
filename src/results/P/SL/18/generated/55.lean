

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  have hP3_open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_open hA_closed
  have hOpen_int : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  exact hP3_open.trans hOpen_int