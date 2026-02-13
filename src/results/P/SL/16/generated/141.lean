

theorem Topology.isOpen_closure_iff_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure A) ↔ interior (closure A) = closure A := by
  constructor
  · intro hOpen
    exact hOpen.interior_eq
  · intro h_eq
    have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h_eq] using hOpenInt