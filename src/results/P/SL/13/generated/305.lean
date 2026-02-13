

theorem Topology.isOpen_iff_interior_eq {X : Type*} [TopologicalSpace X] {U : Set X} :
    IsOpen (U : Set X) ↔ interior U = U := by
  constructor
  · intro hU
    simpa using hU.interior_eq
  · intro h_eq
    have h_open : IsOpen (interior (U : Set X)) := isOpen_interior
    simpa [h_eq] using h_open