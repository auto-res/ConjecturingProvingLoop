

theorem Topology.isOpen_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A ↔ interior A = A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro h_eq
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using hOpenInt