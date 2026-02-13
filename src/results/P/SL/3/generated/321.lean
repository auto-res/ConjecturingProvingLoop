

theorem isOpen_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
  constructor
  · intro hOpen
    exact hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [hEq] using hOpenInt