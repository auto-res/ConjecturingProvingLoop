

theorem interior_eq_self_of_closed_iff_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    interior A = A ↔ IsOpen A := by
  constructor
  · intro hInt
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using hOpenInt
  · intro hOpen
    simpa using hOpen.interior_eq