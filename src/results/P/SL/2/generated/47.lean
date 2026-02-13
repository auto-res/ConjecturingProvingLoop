

theorem isOpen_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A ↔ interior A = A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this