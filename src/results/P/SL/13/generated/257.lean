

theorem Topology.isOpen_closure_iff_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    have h_open_int : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [h_eq] using h_open_int