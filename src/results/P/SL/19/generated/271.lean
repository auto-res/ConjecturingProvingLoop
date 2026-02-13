

theorem Topology.isOpen_closure_iff_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure A) ↔ interior (closure A) = closure A := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hEq] using hOpenInt