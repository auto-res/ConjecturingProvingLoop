

theorem Topology.isOpen_closureInterior_iff_interior_closureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) ↔
      interior (closure (interior A)) = closure (interior A) := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    have h_open_int : IsOpen (interior (closure (interior (A : Set X)))) :=
      isOpen_interior
    simpa [h_eq] using h_open_int