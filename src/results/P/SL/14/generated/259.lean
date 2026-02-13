

theorem Topology.isOpen_closure_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure A := by
  constructor
  · intro hOpen
    simpa [hOpen.interior_eq]
  · intro hEq
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt